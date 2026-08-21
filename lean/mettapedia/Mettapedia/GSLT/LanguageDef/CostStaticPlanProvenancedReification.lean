import Mettapedia.GSLT.LanguageDef.CostStaticPlanCanonicalReification

/-!
# Provenance-bearing reified stops

`CostStaticPlanCanonicalReifiedStop.sourceFVar` accepts an arbitrary
string, but the desired semantic callback is **false** at arbitrary names:
a name colliding with a generated atom name, or held by only one
environment, reifies asymmetrically, and no restoration law relates the
results.  Reachability is what saves the actual producer — every rigid
free variable of an aligned skeleton pair occurs in *both* skeletons —
and this module records that reachability in the carrier instead of
leaving it as an unstated invariant.

Concretely:

* `CanonicalStopRouted` is the stop-alignment shape **without** a rigid
  free-variable constructor;
* `CanonicalStopAligned.routeFVars` reroutes every rigid free-variable
  arm into a stop leaf carrying membership of the name in both root
  free-variable lists — derivable because pattern binders bind only
  de Bruijn indices, so a free variable of any subterm is free in the
  root;
* `CanonicalStopRouted.environmentReifyCanonicalizeByDepths` is the
  reify-and-canonicalize congruence over the routed shape.  Having no
  free-variable arm, it demands **no** callback at unreachable names;
* `CostStaticPlanProvenancedStop` is the refined reified carrier: a plan
  stop, or a source variable **with membership evidence on both sides**;
* `reifiedSourceProvenancedAlignment_of_canonicalize_eq` is the corrected
  composition boundary: the caller's callback is invoked only at plan
  stops and at membership-certified free variables.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open WellSorted

/-- Filling a one-hole context retains every free name of the inserted
pattern. -/
theorem OneHoleContext.mem_freeFvarNames_fill
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    {pattern : Pattern} {name : String}
    (membership : name ∈ pattern.freeFvarNames) :
    name ∈ (context.fill pattern).freeFvarNames := by
  induction context with
  | hole => exact membership
  | apply constructor before inner after inductionHypothesis =>
      simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        Pattern.freeFvarNames, List.mem_flatMap]
      exact ⟨inner.fill pattern, by simp, inductionHypothesis⟩
  | lambda binder inner inductionHypothesis =>
      simpa [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        Pattern.freeFvarNames] using inductionHypothesis
  | multiLambda arity binders inner inductionHypothesis =>
      simpa [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        Pattern.freeFvarNames] using inductionHypothesis
  | substBody inner replacement inductionHypothesis =>
      simpa [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        Pattern.freeFvarNames] using Or.inl inductionHypothesis
  | substReplacement body inner inductionHypothesis =>
      simpa [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        Pattern.freeFvarNames] using Or.inr inductionHypothesis
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨inner.fill pattern, by simp, inductionHypothesis⟩

/-! ## The routed alignment shape -/

mutual
  /-- Stop-aligned descent with no rigid free-variable arm: every free
  variable must enter through the stop relation.  All other constructors
  mirror `CanonicalStopAligned`. -/
  inductive CanonicalStopRouted
      (declaration : ReflectivePresentationDecl)
      (stop : Pattern → Pattern → Prop) : Pattern → Pattern → Prop where
    | leaf {left right : Pattern} (given : stop left right) :
        CanonicalStopRouted declaration stop left right
    | bvar (index : Nat) :
        CanonicalStopRouted declaration stop (.bvar index) (.bvar index)
    | apply {constructor : String}
        (ne : constructor ≠ declaration.quoteConstructor)
        {leftArguments rightArguments : List Pattern}
        (arguments : CanonicalStopRoutedList declaration stop
          leftArguments rightArguments) :
        CanonicalStopRouted declaration stop
          (.apply constructor leftArguments)
          (.apply constructor rightArguments)
    | lambda (binder : Option String) {leftBody rightBody : Pattern}
        (body : CanonicalStopRouted declaration stop leftBody rightBody) :
        CanonicalStopRouted declaration stop (.lambda binder leftBody)
          (.lambda binder rightBody)
    | multiLambda (arity : Nat) (binders : List String)
        {leftBody rightBody : Pattern}
        (body : CanonicalStopRouted declaration stop leftBody rightBody) :
        CanonicalStopRouted declaration stop
          (.multiLambda arity binders leftBody)
          (.multiLambda arity binders rightBody)
    | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
        (body : CanonicalStopRouted declaration stop leftBody rightBody)
        (replacement : CanonicalStopRouted declaration stop leftReplacement
          rightReplacement) :
        CanonicalStopRouted declaration stop
          (.subst leftBody leftReplacement)
          (.subst rightBody rightReplacement)
    | collection {collectionType : CollType}
        (ne : collectionType ≠ declaration.parallelCollection)
        {leftElements rightElements : List Pattern}
        (elements : CanonicalStopRoutedList declaration stop
          leftElements rightElements) :
        CanonicalStopRouted declaration stop
          (.collection collectionType leftElements none)
          (.collection collectionType rightElements none)
    | collectionRest (collectionType : CollType) (rest : String)
        {leftElements rightElements : List Pattern}
        (elements : CanonicalStopRoutedList declaration stop
          leftElements rightElements) :
        CanonicalStopRouted declaration stop
          (.collection collectionType leftElements (some rest))
          (.collection collectionType rightElements (some rest))

  /-- Pointwise companion of `CanonicalStopRouted`. -/
  inductive CanonicalStopRoutedList
      (declaration : ReflectivePresentationDecl)
      (stop : Pattern → Pattern → Prop) :
      List Pattern → List Pattern → Prop where
    | nil : CanonicalStopRoutedList declaration stop [] []
    | cons {leftHead rightHead : Pattern}
        {leftTail rightTail : List Pattern}
        (head : CanonicalStopRouted declaration stop leftHead rightHead)
        (tail : CanonicalStopRoutedList declaration stop leftTail
          rightTail) :
        CanonicalStopRoutedList declaration stop
          (leftHead :: leftTail) (rightHead :: rightTail)
end

/-- A rigid free-variable pair whose name is certified to occur freely in
both fixed root patterns. -/
def MemberFVarPair (leftRootFree rightRootFree : List String)
    (left right : Pattern) : Prop :=
  ∃ name, left = .fvar name ∧ right = .fvar name ∧
    name ∈ leftRootFree ∧ name ∈ rightRootFree

mutual
  /-- Route every rigid free-variable arm of a stop alignment into a
  membership-certified leaf.  The inclusions thread structurally: pattern
  binders bind only de Bruijn indices, so each subterm's free variables
  inject into its parent's. -/
  def CanonicalStopAligned.routeFVars
      {declaration : ReflectivePresentationDecl}
      {stop : Pattern → Pattern → Prop}
      {leftRootFree rightRootFree : List String} :
      ∀ {left right : Pattern},
        CanonicalStopAligned declaration stop left right →
        (∀ name, name ∈ left.freeFvarNames → name ∈ leftRootFree) →
        (∀ name, name ∈ right.freeFvarNames → name ∈ rightRootFree) →
        CanonicalStopRouted declaration
          (fun a b => stop a b ∨
            MemberFVarPair leftRootFree rightRootFree a b)
          left right
    | _, _, .leaf given, _, _ => .leaf (Or.inl given)
    | _, _, .bvar index, _, _ => .bvar index
    | _, _, .fvar name, includeLeft, includeRight =>
        .leaf (Or.inr ⟨name, rfl, rfl,
          includeLeft name (by simp [Pattern.freeFvarNames]),
          includeRight name (by simp [Pattern.freeFvarNames])⟩)
    | _, _, .apply ne arguments, includeLeft, includeRight =>
        .apply ne (CanonicalStopAlignedList.routeFVars arguments
          (fun name mem => includeLeft name
            (by simpa [Pattern.freeFvarNames] using mem))
          (fun name mem => includeRight name
            (by simpa [Pattern.freeFvarNames] using mem)))
    | _, _, .lambda binder body, includeLeft, includeRight =>
        .lambda binder (CanonicalStopAligned.routeFVars body
          (fun name mem => includeLeft name
            (by simpa [Pattern.freeFvarNames] using mem))
          (fun name mem => includeRight name
            (by simpa [Pattern.freeFvarNames] using mem)))
    | _, _, .multiLambda arity binders body, includeLeft, includeRight =>
        .multiLambda arity binders (CanonicalStopAligned.routeFVars body
          (fun name mem => includeLeft name
            (by simpa [Pattern.freeFvarNames] using mem))
          (fun name mem => includeRight name
            (by simpa [Pattern.freeFvarNames] using mem)))
    | _, _, .subst body replacement, includeLeft, includeRight =>
        .subst
          (CanonicalStopAligned.routeFVars body
            (fun name mem => includeLeft name
              (by simp [Pattern.freeFvarNames]; exact Or.inl mem))
            (fun name mem => includeRight name
              (by simp [Pattern.freeFvarNames]; exact Or.inl mem)))
          (CanonicalStopAligned.routeFVars replacement
            (fun name mem => includeLeft name
              (by simp [Pattern.freeFvarNames]; exact Or.inr mem))
            (fun name mem => includeRight name
              (by simp [Pattern.freeFvarNames]; exact Or.inr mem)))
    | _, _, .collection ne elements, includeLeft, includeRight =>
        .collection ne (CanonicalStopAlignedList.routeFVars elements
          (fun name mem => includeLeft name
            (by simpa [Pattern.freeFvarNames] using mem))
          (fun name mem => includeRight name
            (by simpa [Pattern.freeFvarNames] using mem)))
    | _, _, .collectionRest collectionType rest elements, includeLeft,
        includeRight =>
        .collectionRest collectionType rest (CanonicalStopAlignedList.routeFVars elements
          (fun name mem => includeLeft name
            (by simp [Pattern.freeFvarNames]
                exact Or.inl (List.mem_flatMap.mp mem)))
          (fun name mem => includeRight name
            (by simp [Pattern.freeFvarNames]
                exact Or.inl (List.mem_flatMap.mp mem))))

  /-- Listwise companion of `CanonicalStopAligned.routeFVars`. -/
  def CanonicalStopAlignedList.routeFVars
      {declaration : ReflectivePresentationDecl}
      {stop : Pattern → Pattern → Prop}
      {leftRootFree rightRootFree : List String} :
      ∀ {left right : List Pattern},
        CanonicalStopAlignedList declaration stop left right →
        (∀ name, name ∈ left.flatMap Pattern.freeFvarNames →
          name ∈ leftRootFree) →
        (∀ name, name ∈ right.flatMap Pattern.freeFvarNames →
          name ∈ rightRootFree) →
        CanonicalStopRoutedList declaration
          (fun a b => stop a b ∨
            MemberFVarPair leftRootFree rightRootFree a b)
          left right
    | _, _, .nil, _, _ => .nil
    | _, _, .cons head tail, includeLeft, includeRight =>
        .cons
          (CanonicalStopAligned.routeFVars head
            (fun name mem => includeLeft name
              (by simp only [List.flatMap_cons, List.mem_append]
                  exact Or.inl mem))
            (fun name mem => includeRight name
              (by simp only [List.flatMap_cons, List.mem_append]
                  exact Or.inl mem)))
          (CanonicalStopAlignedList.routeFVars tail
            (fun name mem => includeLeft name
              (by simp only [List.flatMap_cons, List.mem_append]
                  exact Or.inr mem))
            (fun name mem => includeRight name
              (by simp only [List.flatMap_cons, List.mem_append]
                  exact Or.inr mem)))
end

/-! ## The congruence over the routed shape -/

mutual
  /-- Reify a routed alignment and pass it through two keyed
  canonicalizers.  There is no free-variable callback: every leaf is a
  stop, so the caller is consulted only at stops. -/
  def CanonicalStopRouted.environmentReifyCanonicalizeByDepths
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {leftOccurrences rightOccurrences : List CostRegionOccurrence}
      {leftTable : TypedCostRegionBoundaryTable source color targetFree
        leftOccurrences}
      {rightTable : TypedCostRegionBoundaryTable source color targetFree
        rightOccurrences}
      {leftValues : TypedCostRegionBoundaryTable.Values source color
        targetFree leftTable}
      {rightValues : TypedCostRegionBoundaryTable.Values source color
        targetFree rightTable}
      {leftRoot rightRoot : Pattern}
      {leftInventory : CostStaticParameterInventory source color targetFree
        leftTable leftValues leftRoot}
      {rightInventory : CostStaticParameterInventory source color targetFree
        rightTable rightValues rightRoot}
      (leftEnvironment : CostStaticAtomEnvironment source color targetFree
        leftInventory)
      (rightEnvironment : CostStaticAtomEnvironment source color targetFree
        rightInventory)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop relation : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth {left right},
        sourceStop left right →
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth (leftEnvironment.reify left))
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth (rightEnvironment.reify right))) :
      ∀ {left right}, CanonicalStopRouted declaration sourceStop left right →
        ∀ availableDepth scopeDepth,
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth (leftEnvironment.reify left))
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth (rightEnvironment.reify right))
    | _, _, .leaf given, availableDepth, scopeDepth =>
        mapStop availableDepth scopeDepth given
    | _, _, .bvar index, availableDepth, scopeDepth => by
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
        exact .bvar index
    | _, _, @CanonicalStopRouted.apply _ _ constructor ne _ _ arguments,
        availableDepth, scopeDepth => by
        have normalizedArguments :=
          CanonicalStopRoutedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop arguments availableDepth scopeDepth
        have notQuoteBeq :
            (constructor == declaration.quoteConstructor) = false :=
          beq_eq_false_iff_ne.mpr ne
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          notQuoteBeq, Bool.false_eq_true, if_false]
        exact .apply constructor normalizedArguments
    | _, _, .lambda binder body, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify,
          canonicalizeByDepths] using
          (PatternLeafAligned.lambda binder
            (CanonicalStopRouted.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop body (availableDepth + 1) (scopeDepth + 1)))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify,
          canonicalizeByDepths] using
          (PatternLeafAligned.multiLambda arity binders
            (CanonicalStopRouted.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop body (availableDepth + arity) (scopeDepth + arity)))
    | _, _, .subst body replacement, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify,
          canonicalizeByDepths] using
          (PatternLeafAligned.subst
            (CanonicalStopRouted.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop body (availableDepth + 1) (scopeDepth + 1))
            (CanonicalStopRouted.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop replacement availableDepth scopeDepth))
    | _, _, @CanonicalStopRouted.collection _ _ collectionType ne _ _
        elements, availableDepth, scopeDepth => by
        have normalizedElements :=
          CanonicalStopRoutedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop elements availableDepth scopeDepth
        have notParallelBeq :
            (collectionType == declaration.parallelCollection) = false :=
          beq_eq_false_iff_ne.mpr ne
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, leftEnvironment.reify_eq_renameFVars,
          rightEnvironment.reify_eq_renameFVars,
          canonicalizeByDepths, canonicalizeListByDepths_eq_map,
          notParallelBeq] using
          (PatternLeafAligned.collection collectionType none
            normalizedElements)
    | _, _, .collectionRest collectionType rest elements, availableDepth,
        scopeDepth => by
        have normalizedElements :=
          CanonicalStopRoutedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop elements availableDepth scopeDepth
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, leftEnvironment.reify_eq_renameFVars,
          rightEnvironment.reify_eq_renameFVars,
          canonicalizeByDepths, canonicalizeListByDepths_eq_map] using
          (PatternLeafAligned.collection collectionType (some rest)
            normalizedElements)

  /-- Listwise companion. -/
  def CanonicalStopRoutedList.environmentReifyCanonicalizeByDepths
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {leftOccurrences rightOccurrences : List CostRegionOccurrence}
      {leftTable : TypedCostRegionBoundaryTable source color targetFree
        leftOccurrences}
      {rightTable : TypedCostRegionBoundaryTable source color targetFree
        rightOccurrences}
      {leftValues : TypedCostRegionBoundaryTable.Values source color
        targetFree leftTable}
      {rightValues : TypedCostRegionBoundaryTable.Values source color
        targetFree rightTable}
      {leftRoot rightRoot : Pattern}
      {leftInventory : CostStaticParameterInventory source color targetFree
        leftTable leftValues leftRoot}
      {rightInventory : CostStaticParameterInventory source color targetFree
        rightTable rightValues rightRoot}
      (leftEnvironment : CostStaticAtomEnvironment source color targetFree
        leftInventory)
      (rightEnvironment : CostStaticAtomEnvironment source color targetFree
        rightInventory)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop relation : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth {left right},
        sourceStop left right →
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth (leftEnvironment.reify left))
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth (rightEnvironment.reify right))) :
      ∀ {left right},
        CanonicalStopRoutedList declaration sourceStop left right →
        ∀ availableDepth scopeDepth,
          PatternLeafAlignedList relation
            (canonicalizeListByDepths leftKey declaration availableDepth
              scopeDepth (left.map leftEnvironment.reify))
            (canonicalizeListByDepths rightKey declaration availableDepth
              scopeDepth (right.map rightEnvironment.reify))
    | _, _, .nil, _, _ => .nil
    | _, _, .cons head tail, availableDepth, scopeDepth =>
        .cons
          (head.environmentReifyCanonicalizeByDepths leftEnvironment
            rightEnvironment leftKey rightKey declaration mapStop
            availableDepth scopeDepth)
          (tail.environmentReifyCanonicalizeByDepths leftEnvironment
            rightEnvironment leftKey rightKey declaration mapStop
            availableDepth scopeDepth)
end

mutual
  def CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : FreeTypeContext}
      {leftOccurrences rightOccurrences : List CostRegionOccurrence}
      {leftTable : TypedCostRegionBoundaryTable source color targetFree leftOccurrences}
      {rightTable : TypedCostRegionBoundaryTable source color targetFree rightOccurrences}
      {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree leftTable}
      {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree rightTable}
      {leftRoot rightRoot : Pattern}
      {leftInventory : CostStaticParameterInventory source color targetFree
        leftTable leftValues leftRoot}
      {rightInventory : CostStaticParameterInventory source color targetFree
        rightTable rightValues rightRoot}
      (leftEnvironment : CostStaticAtomEnvironment source color targetFree leftInventory)
      (rightEnvironment : CostStaticAtomEnvironment source color targetFree rightInventory)
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth rootDepth {left right},
        sourceStop left right →
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration := costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApex source cospan targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
                    (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
                    (rightEnvironment.reify right)))))) :
      ∀ {left right}, CanonicalStopRouted declaration sourceStop left right →
        ∀ availableDepth scopeDepth rootDepth,
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration := costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApex source cospan targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
                    (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
                    (rightEnvironment.reify right)))))
    | _, _, .leaf given, availableDepth, scopeDepth, rootDepth =>
        mapStop availableDepth scopeDepth rootDepth given
    | _, _, .bvar index, _, scopeDepth, rootDepth => by
        apply CostStaticAtomKeyCospan.CommonRestorationApex.of_eq
          (source := source) (leftEnvironment.semanticKeyCospan rightEnvironment)
          (costStaticReflectivePresentationDecl source color declaration) rootDepth
        simp [Pattern.renameFVars, canonicalizeByDepths, mapPattern,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticBinderThinning.thickenAmbientBVars]
    | _, _, @CanonicalStopRouted.apply _ _ constructor ne _ _ arguments,
        availableDepth, scopeDepth, rootDepth => by
        let mappedConstructor := (color.symbols source).constructor constructor
        let childRootDepth :=
          if ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile mappedConstructor then 0 else rootDepth
        have normalizedArguments :=
          CanonicalStopRoutedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey declaration
            mapStop arguments availableDepth scopeDepth childRootDepth
        have notQuoteBeq : (constructor == declaration.quoteConstructor) = false :=
          beq_eq_false_iff_ne.mpr ne
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          finishNormalizeReflectiveApply, notQuoteBeq, Bool.false_eq_true,
          if_false, mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith]
        apply CostStaticAtomKeyCospan.CommonRestorationApex.apply mappedConstructor
        simpa [mapPatternList_eq_map, List.map_map, Function.comp_def,
          childRootDepth, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using normalizedArguments
    | _, _, .lambda binder body, availableDepth, scopeDepth, rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.lambda binder
            (CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey declaration
              mapStop body (availableDepth + 1) (scopeDepth + 1) (rootDepth + 1)))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth,
        rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.multiLambda binders
            (CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey declaration
              mapStop body (availableDepth + arity) (scopeDepth + arity)
                (rootDepth + arity)))
    | _, _, .subst body replacement, availableDepth, scopeDepth, rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.subst
            (CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey declaration
              mapStop body (availableDepth + 1) (scopeDepth + 1) (rootDepth + 1))
            (CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey declaration
              mapStop replacement availableDepth scopeDepth rootDepth))
    | _, _, @CanonicalStopRouted.collection _ _ collectionType ne _ _ elements,
        availableDepth, scopeDepth, rootDepth => by
        have normalizedElements :=
          CanonicalStopRoutedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey declaration
            mapStop elements availableDepth scopeDepth rootDepth
        have notParallelBeq :
            (collectionType == declaration.parallelCollection) = false :=
          beq_eq_false_iff_ne.mpr ne
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith, notParallelBeq] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.collection
            collectionType none normalizedElements)
    | _, _, .collectionRest collectionType rest elements, availableDepth,
        scopeDepth, rootDepth => by
        have normalizedElements :=
          CanonicalStopRoutedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey declaration
            mapStop elements availableDepth scopeDepth rootDepth
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.collection
            collectionType (some rest) normalizedElements)

  /-- Listwise companion of
  `CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths`. -/
  def CanonicalStopRoutedList.environmentMapThickenCanonicalizeCommonApexByDepths
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : FreeTypeContext}
      {leftOccurrences rightOccurrences : List CostRegionOccurrence}
      {leftTable : TypedCostRegionBoundaryTable source color targetFree leftOccurrences}
      {rightTable : TypedCostRegionBoundaryTable source color targetFree rightOccurrences}
      {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree leftTable}
      {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree rightTable}
      {leftRoot rightRoot : Pattern}
      {leftInventory : CostStaticParameterInventory source color targetFree leftTable leftValues leftRoot}
      {rightInventory : CostStaticParameterInventory source color targetFree rightTable rightValues rightRoot}
      (leftEnvironment : CostStaticAtomEnvironment source color targetFree leftInventory)
      (rightEnvironment : CostStaticAtomEnvironment source color targetFree rightInventory)
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth rootDepth {left right},
        sourceStop left right →
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration := costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApex source cospan targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
                    (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
                    (rightEnvironment.reify right)))))) :
      ∀ {left right}, CanonicalStopRoutedList declaration sourceStop left right →
        ∀ availableDepth scopeDepth rootDepth,
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration := costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApexList source cospan targetDeclaration rootDepth
            ((canonicalizeListByDepths leftKey declaration availableDepth scopeDepth
              (left.map leftEnvironment.reify)).map
                (fun pattern => cospan.reifyLeft leftEnvironment.lookupAtom?
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern))))
            ((canonicalizeListByDepths rightKey declaration availableDepth scopeDepth
              (right.map rightEnvironment.reify)).map
                (fun pattern => cospan.reifyRight rightEnvironment.lookupAtom?
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern))))
    | _, _, .nil, _, _, rootDepth => .nil rootDepth
    | _, _, .cons head tail, availableDepth, scopeDepth, rootDepth =>
        .cons
          (CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey declaration
            mapStop head availableDepth scopeDepth rootDepth)
          (CanonicalStopRoutedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey declaration
            mapStop tail availableDepth scopeDepth rootDepth)
end


/-! ## The provenanced reified carrier and composition boundary -/

/-- The refined reified stop: a plan stop with reached-plan provenance, or
a rigid free variable **certified to occur freely in both skeletons**.
Nothing else can reach a semantic callback built on this carrier. -/
inductive CostStaticPlanProvenancedStop
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop) : Pattern → Pattern → Prop where
  | plan {left right : Pattern}
      (stop : CostStaticPlanCanonicalStop leftNode.plan rightNode.plan
        declaration rawDeclaration rawStop left right) :
      CostStaticPlanProvenancedStop leftNode rightNode leftEnvironment
        rightEnvironment declaration rawDeclaration rawStop
        (leftEnvironment.reify left) (rightEnvironment.reify right)
  | sourceFVar (name : String)
      (leftMember : name ∈ leftNode.skeleton.1.freeFvarNames)
      (rightMember : name ∈ rightNode.skeleton.1.freeFvarNames) :
      CostStaticPlanProvenancedStop leftNode rightNode leftEnvironment
        rightEnvironment declaration rawDeclaration rawStop
        (.fvar (leftEnvironment.reifyName name))
        (.fvar (rightEnvironment.reifyName name))

namespace CostStaticRegionNode

/-- The corrected composition boundary from an explicit raw stop alignment:
plan descent, membership-certified free-variable routing, semantic-atom
reification, and keyed canonical congruence.  The declaration governing raw
collapse may differ from the declaration governing source-frame descent. -/
noncomputable def reifiedSourceProvenancedAlignment_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftNode.term.1
      rightNode.term.1)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    {relation : Pattern → Pattern → Prop}
    (callback : ∀ callbackAvailable callbackScope {left right},
      CostStaticPlanProvenancedStop leftNode rightNode leftEnvironment
          rightEnvironment
          declaration rawDeclaration rawStop
          left right →
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration callbackAvailable
            callbackScope left)
          (canonicalizeByDepths rightKey declaration callbackAvailable
            callbackScope right)) :
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
        (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
        (rightNode.reifiedSourceFrame rightEnvironment).1) := by
  have planAligned := leftNode.sourceCanonicalStopAligned_of_rawAlignment
    collectionDeterministic declaration rawDeclaration rightNode sameBound
      sameSort rawAligned
  have routed := CanonicalStopAligned.routeFVars planAligned
    (leftRootFree := leftNode.skeleton.1.freeFvarNames)
    (rightRootFree := rightNode.skeleton.1.freeFvarNames)
    (fun _ mem => mem) (fun _ mem => mem)
  have reified :=
    CanonicalStopRouted.environmentReifyCanonicalizeByDepths
      leftEnvironment rightEnvironment leftKey rightKey declaration
      (sourceStop := fun a b =>
        CostStaticPlanCanonicalStop leftNode.plan rightNode.plan
            declaration rawDeclaration rawStop
            a b ∨
          MemberFVarPair leftNode.skeleton.1.freeFvarNames
            rightNode.skeleton.1.freeFvarNames a b)
      (fun callbackAvailable callbackScope {left right} stopped => by
        rcases stopped with planStop | ⟨name, leftEq, rightEq, leftMember,
          rightMember⟩
        · exact callback callbackAvailable callbackScope
            (CostStaticPlanProvenancedStop.plan planStop)
        · subst leftEq
          subst rightEq
          simpa only [CostStaticAtomEnvironment.reify] using
            callback callbackAvailable callbackScope
              (CostStaticPlanProvenancedStop.sourceFVar name leftMember
                rightMember))
      routed availableDepth scopeDepth
  simpa only [reifiedSourceFrame_pattern] using reified

/-- Route plan stops and membership-certified source variables into one
target-coloured common-restoration apex. Endpoint thinning equality is
transported explicitly; it is never treated as definitional equality. -/
noncomputable def reifiedSourceProvenancedCommonApex_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftNode.term.1
      rightNode.term.1)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth rootDepth : Nat)
    (callback : ∀ callbackAvailable callbackScope callbackRoot
        {left right},
      CostStaticPlanProvenancedStop leftNode rightNode leftEnvironment
          rightEnvironment declaration rawDeclaration rawStop left right →
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration :=
          costStaticReflectivePresentationDecl source color declaration
        CostStaticAtomKeyCospan.CommonRestorationApex source cospan
          targetDeclaration callbackRoot
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftNode.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols source)
                (canonicalizeByDepths leftKey declaration callbackAvailable
                  callbackScope left))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightNode.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols source)
                (canonicalizeByDepths rightKey declaration callbackAvailable
                  callbackScope right))))) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration :=
      costStaticReflectivePresentationDecl source color declaration
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan
      targetDeclaration rootDepth
      (cospan.reifyLeft leftEnvironment.lookupAtom?
        (leftNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols source)
            (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
              (leftNode.reifiedSourceFrame leftEnvironment).1))))
      (cospan.reifyRight rightEnvironment.lookupAtom?
        (rightNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols source)
            (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
              (rightNode.reifiedSourceFrame rightEnvironment).1)))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration :=
    costStaticReflectivePresentationDecl source color declaration
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftNode.thinning.thickenAmbientBVars depth pattern =
        rightNode.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using
      congrArg
        (fun targetBound =>
          (CostStaticBinderThinning.ofTargetThinning source color targetBound)
            |>.thickenAmbientBVars depth pattern)
        sameBound
  have planAligned := leftNode.sourceCanonicalStopAligned_of_rawAlignment
    collectionDeterministic declaration rawDeclaration rightNode sameBound
      sameSort rawAligned
  have routed := CanonicalStopAligned.routeFVars planAligned
    (leftRootFree := leftNode.skeleton.1.freeFvarNames)
    (rightRootFree := rightNode.skeleton.1.freeFvarNames)
    (fun _ mem => mem) (fun _ mem => mem)
  have reified :=
    CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
      leftEnvironment rightEnvironment leftNode.thinning leftKey rightKey
      declaration
      (sourceStop := fun a b =>
        CostStaticPlanCanonicalStop leftNode.plan rightNode.plan declaration
            rawDeclaration rawStop a b ∨
          MemberFVarPair leftNode.skeleton.1.freeFvarNames
            rightNode.skeleton.1.freeFvarNames a b)
      (fun callbackAvailable callbackScope callbackRoot {left right} stopped => by
        have endpointApex : CostStaticAtomKeyCospan.CommonRestorationApex source
            cospan targetDeclaration callbackRoot
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (leftNode.thinning.thickenAmbientBVars callbackScope
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration callbackAvailable
                    callbackScope (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (rightNode.thinning.thickenAmbientBVars callbackScope
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration callbackAvailable
                    callbackScope (rightEnvironment.reify right))))) := by
          rcases stopped with planStop | ⟨name, leftEq, rightEq, leftMember,
            rightMember⟩
          · exact callback callbackAvailable callbackScope callbackRoot
              (CostStaticPlanProvenancedStop.plan planStop)
          · subst leftEq
            subst rightEq
            simpa only [CostStaticAtomEnvironment.reify] using
              callback callbackAvailable callbackScope callbackRoot
                (CostStaticPlanProvenancedStop.sourceFVar name leftMember
                  rightMember)
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
          endpointApex
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq callbackScope
            (mapPattern (color.symbols source)
              (canonicalizeByDepths rightKey declaration callbackAvailable
                callbackScope (rightEnvironment.reify right)))).symm)
      routed availableDepth scopeDepth rootDepth
  have sourceApex : CostStaticAtomKeyCospan.CommonRestorationApex source cospan
      targetDeclaration rootDepth
      (cospan.reifyLeft leftEnvironment.lookupAtom?
        (leftNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols source)
            (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
              (leftNode.reifiedSourceFrame leftEnvironment).1))))
      (cospan.reifyRight rightEnvironment.lookupAtom?
        (leftNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols source)
            (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
              (rightNode.reifiedSourceFrame rightEnvironment).1)))) := by
    simpa only [reifiedSourceFrame_pattern] using reified
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _ sourceApex
  exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
    (thickenEq scopeDepth
      (mapPattern (color.symbols source)
        (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
          (rightNode.reifiedSourceFrame rightEnvironment).1)))


/-- Same-declaration specialization obtained from equality of raw canonical
forms. -/
noncomputable def reifiedSourceProvenancedAlignment_of_canonicalize_eq
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl source color declaration)
          leftNode.term.1 =
        canonicalize
          (costStaticReflectivePresentationDecl source color declaration)
          rightNode.term.1)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    {relation : Pattern → Pattern → Prop}
    (callback : ∀ callbackAvailable callbackScope {left right},
      CostStaticPlanProvenancedStop leftNode rightNode leftEnvironment
          rightEnvironment
          declaration
          (costStaticReflectivePresentationDecl source color declaration)
          (fun candidateLeft candidateRight =>
            (CollapsingRoot
                (costStaticReflectivePresentationDecl source color
                  declaration)
                candidateLeft ∨
              CollapsingRoot
                (costStaticReflectivePresentationDecl source color
                  declaration)
                candidateRight) ∧
            canonicalize
                (costStaticReflectivePresentationDecl source color
                  declaration)
                candidateLeft =
              canonicalize
                (costStaticReflectivePresentationDecl source color
                  declaration)
                candidateRight)
          left right →
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration callbackAvailable
            callbackScope left)
          (canonicalizeByDepths rightKey declaration callbackAvailable
            callbackScope right)) :
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
        (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
        (rightNode.reifiedSourceFrame rightEnvironment).1) :=
  leftNode.reifiedSourceProvenancedAlignment_of_rawAlignment
    collectionDeterministic declaration
    (costStaticReflectivePresentationDecl source color declaration)
    rightNode leftEnvironment rightEnvironment sameBound sameSort
    (canonicalStopAligned_of_canonicalize_eq
      (costStaticReflectivePresentationDecl source color declaration)
      canonical)
    leftKey rightKey availableDepth scopeDepth callback

end CostStaticRegionNode

/-! ## Canary -/

/-- The refined constructor refuses arbitrary names: without membership on
both sides, no source-variable stop can be formed.  This is the carrier
correction — the semantic callback is never consulted at a name whose
reachability is unestablished. -/
example
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop) (name : String)
    (leftMember : name ∈ leftNode.skeleton.1.freeFvarNames)
    (rightMember : name ∈ rightNode.skeleton.1.freeFvarNames) :
    CostStaticPlanProvenancedStop leftNode rightNode leftEnvironment
      rightEnvironment declaration rawDeclaration rawStop
      (.fvar (leftEnvironment.reifyName name))
      (.fvar (rightEnvironment.reifyName name)) :=
  .sourceFVar name leftMember rightMember

end Mettapedia.GSLT.LanguageDef
