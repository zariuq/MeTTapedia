import Mettapedia.GSLT.LanguageDef.CostSemanticAtomAlignment
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Reify and restoration congruence over explicit semantic leaves

Two static skeletons produced for the two endpoints of one generated edge
may differ at finitely selected semantic leaves: a changed boundary child can
change its content-keyed name, become a bound variable, or restore to a
structured value, while the surrounding constructors and binders remain
explicit.  Reification into a common semantic apex and supported restoration
then propagate the supplied leaf equalities structurally.  The older
free-variable-only congruence is retained as a derived special case.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  /-- Structural identity up to a relation on free-variable spellings. -/
  inductive FvarAligned (relation : String → String → Prop) :
      Pattern → Pattern → Prop where
    | bvar (index : Nat) : FvarAligned relation (.bvar index) (.bvar index)
    | fvar {left right : String} (related : relation left right) :
        FvarAligned relation (.fvar left) (.fvar right)
    | apply (constructor : String)
        {leftArguments rightArguments : List Pattern}
        (arguments : FvarAlignedList relation leftArguments rightArguments) :
        FvarAligned relation (.apply constructor leftArguments)
          (.apply constructor rightArguments)
    | lambda (binder : Option String) {leftBody rightBody : Pattern}
        (body : FvarAligned relation leftBody rightBody) :
        FvarAligned relation (.lambda binder leftBody)
          (.lambda binder rightBody)
    | multiLambda (arity : Nat) (binders : List String)
        {leftBody rightBody : Pattern}
        (body : FvarAligned relation leftBody rightBody) :
        FvarAligned relation (.multiLambda arity binders leftBody)
          (.multiLambda arity binders rightBody)
    | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
        (body : FvarAligned relation leftBody rightBody)
        (replacement : FvarAligned relation leftReplacement
          rightReplacement) :
        FvarAligned relation (.subst leftBody leftReplacement)
          (.subst rightBody rightReplacement)
    | collection (collectionType : CollType) (rest : Option String)
        {leftElements rightElements : List Pattern}
        (elements : FvarAlignedList relation leftElements rightElements) :
        FvarAligned relation (.collection collectionType leftElements rest)
          (.collection collectionType rightElements rest)

  /-- Pointwise spelling alignment for pattern lists. -/
  inductive FvarAlignedList (relation : String → String → Prop) :
      List Pattern → List Pattern → Prop where
    | nil : FvarAlignedList relation [] []
    | cons {leftHead rightHead : Pattern}
        {leftTail rightTail : List Pattern}
        (head : FvarAligned relation leftHead rightHead)
        (tail : FvarAlignedList relation leftTail rightTail) :
        FvarAlignedList relation (leftHead :: leftTail)
          (rightHead :: rightTail)
end

mutual
  /-- Structural identity up to explicitly selected semantic leaves.

  Unlike `FvarAligned`, a leaf may relate a rigid boundary variable to a
  bound variable or to a structured value.  Free variables have no implicit
  reflexivity constructor: every free-variable leaf must be justified by the
  supplied semantic relation. -/
  inductive PatternLeafAligned (relation : Pattern → Pattern → Prop) :
      Pattern → Pattern → Prop where
    | leaf {left right : Pattern} (related : relation left right) :
        PatternLeafAligned relation left right
    | bvar (index : Nat) :
        PatternLeafAligned relation (.bvar index) (.bvar index)
    | apply (constructor : String)
        {leftArguments rightArguments : List Pattern}
        (arguments : PatternLeafAlignedList relation leftArguments
          rightArguments) :
        PatternLeafAligned relation (.apply constructor leftArguments)
          (.apply constructor rightArguments)
    | lambda (binder : Option String) {leftBody rightBody : Pattern}
        (body : PatternLeafAligned relation leftBody rightBody) :
        PatternLeafAligned relation (.lambda binder leftBody)
          (.lambda binder rightBody)
    | multiLambda (arity : Nat) (binders : List String)
        {leftBody rightBody : Pattern}
        (body : PatternLeafAligned relation leftBody rightBody) :
        PatternLeafAligned relation (.multiLambda arity binders leftBody)
          (.multiLambda arity binders rightBody)
    | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
        (body : PatternLeafAligned relation leftBody rightBody)
        (replacement : PatternLeafAligned relation leftReplacement
          rightReplacement) :
        PatternLeafAligned relation (.subst leftBody leftReplacement)
          (.subst rightBody rightReplacement)
    | collection (collectionType : CollType) (rest : Option String)
        {leftElements rightElements : List Pattern}
        (elements : PatternLeafAlignedList relation leftElements
          rightElements) :
        PatternLeafAligned relation
          (.collection collectionType leftElements rest)
          (.collection collectionType rightElements rest)

  /-- Pointwise companion for semantic-leaf alignment. -/
  inductive PatternLeafAlignedList (relation : Pattern → Pattern → Prop) :
      List Pattern → List Pattern → Prop where
    | nil : PatternLeafAlignedList relation [] []
    | cons {leftHead rightHead : Pattern}
        {leftTail rightTail : List Pattern}
        (head : PatternLeafAligned relation leftHead rightHead)
        (tail : PatternLeafAlignedList relation leftTail rightTail) :
        PatternLeafAlignedList relation (leftHead :: leftTail)
          (rightHead :: rightTail)
end

mutual
  /-- Free-variable alignment is the special case of semantic-leaf alignment
  whose selected leaves receive an explicit semantic witness. -/
  def FvarAligned.toPatternLeafAligned
      {nameRelation : String → String → Prop}
      {leafRelation : Pattern → Pattern → Prop}
      (lift : ∀ {leftName rightName}, nameRelation leftName rightName →
        leafRelation (.fvar leftName) (.fvar rightName)) :
      ∀ {left right : Pattern}, FvarAligned nameRelation left right →
        PatternLeafAligned leafRelation left right
    | _, _, .bvar index => .bvar index
    | _, _, .fvar related => .leaf (lift related)
    | _, _, .apply constructor arguments =>
        .apply constructor (arguments.toPatternLeafAligned lift)
    | _, _, .lambda binder body =>
        .lambda binder (body.toPatternLeafAligned lift)
    | _, _, .multiLambda arity binders body =>
        .multiLambda arity binders (body.toPatternLeafAligned lift)
    | _, _, .subst body replacement =>
        .subst (body.toPatternLeafAligned lift)
          (replacement.toPatternLeafAligned lift)
    | _, _, .collection collectionType rest elements =>
        .collection collectionType rest
          (elements.toPatternLeafAligned lift)

  /-- Listwise companion of `FvarAligned.toPatternLeafAligned`. -/
  def FvarAlignedList.toPatternLeafAligned
      {nameRelation : String → String → Prop}
      {leafRelation : Pattern → Pattern → Prop}
      (lift : ∀ {leftName rightName}, nameRelation leftName rightName →
        leafRelation (.fvar leftName) (.fvar rightName)) :
      ∀ {left right : List Pattern}, FvarAlignedList nameRelation left right →
        PatternLeafAlignedList leafRelation left right
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (head.toPatternLeafAligned lift)
          (tail.toPatternLeafAligned lift)
end

mutual
  /-- Structural reflexivity requires evidence only for free-variable leaves.
  Bound variables and all constructors are aligned intrinsically. -/
  theorem PatternLeafAligned.refl {relation : Pattern → Pattern → Prop}
      (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name)) :
      ∀ pattern, PatternLeafAligned relation pattern pattern
    | .bvar index => .bvar index
    | .fvar name => .leaf (fvarReflexive name)
    | .apply constructor arguments =>
        .apply constructor
          (PatternLeafAlignedList.refl fvarReflexive arguments)
    | .lambda binder body =>
        .lambda binder (PatternLeafAligned.refl fvarReflexive body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders
          (PatternLeafAligned.refl fvarReflexive body)
    | .subst body replacement =>
        .subst (PatternLeafAligned.refl fvarReflexive body)
          (PatternLeafAligned.refl fvarReflexive replacement)
    | .collection collectionType elements rest =>
        .collection collectionType rest
          (PatternLeafAlignedList.refl fvarReflexive elements)

  /-- Listwise structural reflexivity. -/
  theorem PatternLeafAlignedList.refl
      {relation : Pattern → Pattern → Prop}
      (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name)) :
      ∀ patterns, PatternLeafAlignedList relation patterns patterns
    | [] => .nil
    | pattern :: patterns =>
        .cons (PatternLeafAligned.refl fvarReflexive pattern)
          (PatternLeafAlignedList.refl fvarReflexive patterns)
end

/-- Concatenate two pointwise semantic-leaf alignments. -/
def PatternLeafAlignedList.append
    {relation : Pattern → Pattern → Prop} :
    ∀ {leftPrefix rightPrefix leftSuffix rightSuffix : List Pattern},
      PatternLeafAlignedList relation leftPrefix rightPrefix →
      PatternLeafAlignedList relation leftSuffix rightSuffix →
      PatternLeafAlignedList relation (leftPrefix ++ leftSuffix)
        (rightPrefix ++ rightSuffix)
  | _, _, _, _, .nil, suffix => suffix
  | _, _, _, _, .cons head tail, suffix =>
      .cons head (PatternLeafAlignedList.append tail suffix)

/-! ## Local evidence for a one-hole context -/

/-- Semantic-leaf reflexivity for exactly the fixed pieces of one one-hole
context.  This avoids asking for a global reflexivity law on names that do
not occur in the context. -/
inductive PatternLeafAlignedContext (relation : Pattern → Pattern → Prop) :
    Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext → Type where
  | hole : PatternLeafAlignedContext relation .hole
  | apply (constructor : String) (before : List Pattern)
      {inner : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
      (after : List Pattern)
      (beforeAligned : PatternLeafAlignedList relation before before)
      (innerAligned : PatternLeafAlignedContext relation inner)
      (afterAligned : PatternLeafAlignedList relation after after) :
      PatternLeafAlignedContext relation
        (.apply constructor before inner after)
  | lambda (binder : Option String)
      {inner : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
      (innerAligned : PatternLeafAlignedContext relation inner) :
      PatternLeafAlignedContext relation (.lambda binder inner)
  | multiLambda (arity : Nat) (binders : List String)
      {inner : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
      (innerAligned : PatternLeafAlignedContext relation inner) :
      PatternLeafAlignedContext relation
        (.multiLambda arity binders inner)
  | substBody
      {inner : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
      (replacement : Pattern)
      (innerAligned : PatternLeafAlignedContext relation inner)
      (replacementAligned : PatternLeafAligned relation replacement
        replacement) :
      PatternLeafAlignedContext relation (.substBody inner replacement)
  | substReplacement (body : Pattern)
      {inner : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
      (bodyAligned : PatternLeafAligned relation body body)
      (innerAligned : PatternLeafAlignedContext relation inner) :
      PatternLeafAlignedContext relation (.substReplacement body inner)
  | collection (collectionType : CollType) (before : List Pattern)
      {inner : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
      (after : List Pattern) (rest : Option String)
      (beforeAligned : PatternLeafAlignedList relation before before)
      (innerAligned : PatternLeafAlignedContext relation inner)
      (afterAligned : PatternLeafAlignedList relation after after) :
      PatternLeafAlignedContext relation
        (.collection collectionType before inner after rest)

namespace PatternLeafAlignedContext

/-- A global free-variable reflexivity law yields the local certificate for
any particular context.  This is a convenience constructor, not a premise of
the local congruence theorem. -/
def ofFvarReflexive {relation : Pattern → Pattern → Prop}
    (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name)) :
    ∀ context, PatternLeafAlignedContext relation context
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply constructor before after
        (PatternLeafAlignedList.refl fvarReflexive before)
        (ofFvarReflexive fvarReflexive inner)
        (PatternLeafAlignedList.refl fvarReflexive after)
  | .lambda binder inner =>
      .lambda binder (ofFvarReflexive fvarReflexive inner)
  | .multiLambda arity binders inner =>
      .multiLambda arity binders (ofFvarReflexive fvarReflexive inner)
  | .substBody inner replacement =>
      .substBody replacement (ofFvarReflexive fvarReflexive inner)
        (PatternLeafAligned.refl fvarReflexive replacement)
  | .substReplacement body inner =>
      .substReplacement body (PatternLeafAligned.refl fvarReflexive body)
        (ofFvarReflexive fvarReflexive inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType before after rest
        (PatternLeafAlignedList.refl fvarReflexive before)
        (ofFvarReflexive fvarReflexive inner)
        (PatternLeafAlignedList.refl fvarReflexive after)

/-- Fill a locally certified context with one aligned semantic leaf. -/
def fill {relation : Pattern → Pattern → Prop} :
    ∀ {context left right}, PatternLeafAlignedContext relation context →
      PatternLeafAligned relation left right →
        PatternLeafAligned relation (context.fill left) (context.fill right)
  | _, _, _, .hole, aligned => aligned
  | _, _, _, .apply constructor before after beforeAligned innerAligned
      afterAligned, aligned =>
      .apply constructor
        (beforeAligned.append
          (.cons (innerAligned.fill aligned) afterAligned))
  | _, _, _, .lambda binder innerAligned, aligned =>
      .lambda binder (innerAligned.fill aligned)
  | _, _, _, .multiLambda arity binders innerAligned, aligned =>
      .multiLambda arity binders (innerAligned.fill aligned)
  | _, _, _, .substBody replacement innerAligned replacementAligned,
      aligned =>
      .subst (innerAligned.fill aligned) replacementAligned
  | _, _, _, .substReplacement body bodyAligned innerAligned, aligned =>
      .subst bodyAligned (innerAligned.fill aligned)
  | _, _, _, .collection collectionType before after rest beforeAligned
      innerAligned afterAligned, aligned =>
      .collection collectionType rest
        (beforeAligned.append
          (.cons (innerAligned.fill aligned) afterAligned))

end PatternLeafAlignedContext

/-- A shared one-hole context preserves semantic-leaf alignment.  Fixed
siblings need only the explicit free-variable reflexivity evidence used by
`PatternLeafAligned.refl`. -/
theorem PatternLeafAligned.fill
    {relation : Pattern → Pattern → Prop}
    (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name)) :
    ∀ (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
      {left right : Pattern},
      PatternLeafAligned relation left right →
        PatternLeafAligned relation (context.fill left) (context.fill right)
  | context, _, _, aligned =>
      (PatternLeafAlignedContext.ofFvarReflexive fvarReflexive context).fill
        aligned

/-- Semantic-leaf alignment genuinely requires a supplied relation at a
free-variable leaf; it cannot manufacture reflexivity from an empty
relation. -/
theorem not_patternLeafAligned_fvar_without_relation (name : String) :
    ¬ PatternLeafAligned (fun _ _ => False) (.fvar name) (.fvar name) := by
  intro aligned
  cases aligned with
  | leaf related => exact related

mutual
  /-- Reflexivity along a reflexive spelling relation. -/
  theorem FvarAligned.refl {relation : String → String → Prop}
      (reflexive : ∀ name, relation name name) :
      ∀ pattern, FvarAligned relation pattern pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar (reflexive name)
    | .apply constructor arguments =>
        .apply constructor (FvarAlignedList.refl reflexive arguments)
    | .lambda binder body => .lambda binder (FvarAligned.refl reflexive body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (FvarAligned.refl reflexive body)
    | .subst body replacement =>
        .subst (FvarAligned.refl reflexive body)
          (FvarAligned.refl reflexive replacement)
    | .collection collectionType elements rest =>
        .collection collectionType rest
          (FvarAlignedList.refl reflexive elements)

  /-- Listwise reflexivity along a reflexive spelling relation. -/
  theorem FvarAlignedList.refl {relation : String → String → Prop}
      (reflexive : ∀ name, relation name name) :
      ∀ patterns, FvarAlignedList relation patterns patterns
    | [] => .nil
    | pattern :: patterns =>
        .cons (FvarAligned.refl reflexive pattern)
          (FvarAlignedList.refl reflexive patterns)
end

namespace CostStaticAtomKeyCospan

mutual
  /-- Reification through a common semantic apex is invariant across aligned
  free-variable spellings whenever every related pair of names resolves on
  both sides to one common leg index. -/
  theorem reifyWith_eq_of_fvarAligned
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      {relation : String → String → Prop}
      (matched : ∀ {leftName rightName : String},
        relation leftName rightName →
        ∃ leftSlot rightSlot,
          leftResolve leftName = some leftSlot ∧
            rightResolve rightName = some rightSlot ∧
            leftLeg leftSlot = rightLeg rightSlot)
      {leftPattern rightPattern : Pattern}
      (aligned : FvarAligned relation leftPattern rightPattern) :
      cospan.reifyWith leftResolve leftLeg leftPattern =
        cospan.reifyWith rightResolve rightLeg rightPattern :=
    match aligned with
    | .bvar index => by simp [reifyWith]
    | .fvar related => by
        obtain ⟨leftSlot, rightSlot, leftResolved, rightResolved, legsEq⟩ :=
          matched related
        simp [reifyWith, leftResolved, rightResolved, legsEq]
    | .apply constructor arguments => by
        simp only [reifyWith, Pattern.apply.injEq, true_and]
        exact reifyWithList_eq_of_fvarAlignedList cospan leftResolve
          rightResolve leftLeg rightLeg matched arguments
    | .lambda binder body => by
        simp only [reifyWith, Pattern.lambda.injEq, true_and]
        exact reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
          leftLeg rightLeg matched body
    | .multiLambda arity binders body => by
        simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
        exact reifyWith_eq_of_fvarAligned cospan leftResolve
          rightResolve leftLeg rightLeg matched body
    | .subst body replacement => by
        simp only [reifyWith, Pattern.subst.injEq]
        exact ⟨reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
            leftLeg rightLeg matched body,
          reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
            leftLeg rightLeg matched replacement⟩
    | .collection collectionType rest elements => by
        simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
        exact reifyWithList_eq_of_fvarAlignedList cospan leftResolve
          rightResolve leftLeg rightLeg matched elements

  /-- Listwise companion of the reification congruence. -/
  theorem reifyWithList_eq_of_fvarAlignedList
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      {relation : String → String → Prop}
      (matched : ∀ {leftName rightName : String},
        relation leftName rightName →
        ∃ leftSlot rightSlot,
          leftResolve leftName = some leftSlot ∧
            rightResolve rightName = some rightSlot ∧
            leftLeg leftSlot = rightLeg rightSlot)
      {leftPatterns rightPatterns : List Pattern}
      (aligned : FvarAlignedList relation leftPatterns rightPatterns) :
      leftPatterns.map (cospan.reifyWith leftResolve leftLeg) =
        rightPatterns.map (cospan.reifyWith rightResolve rightLeg) :=
    match aligned with
    | .nil => rfl
    | .cons head tail => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
            leftLeg rightLeg matched head,
          reifyWithList_eq_of_fvarAlignedList cospan leftResolve rightResolve
            leftLeg rightLeg matched tail⟩
end

end CostStaticAtomKeyCospan

/-- Canonical-frame free-variable alignment is sufficient to compare the
two original endpoint frames after reification into a common semantic
namespace and re-canonicalization.

Each endpoint may use a different finite name map.  The factor theorem for
free-variable renaming absorbs the resulting change in parallel sort order;
`FvarAligned` is used only between the already-canonical source frames. -/
theorem CostStaticAtomEnvironment.canonicalize_commonReification_eq_of_aligned
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin left.atomCount -> Fin cospan.commonKeys.length)
    (rightLeg : Fin right.atomCount -> Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    {relation : String -> String -> Prop}
    (matched : ∀ {leftName rightName : String},
      relation leftName rightName ->
      ∃ leftSlot rightSlot,
        left.lookupAtom? leftName = some leftSlot ∧
          right.lookupAtom? rightName = some rightSlot ∧
          leftLeg leftSlot = rightLeg rightSlot)
    {leftPattern rightPattern : Pattern}
    (aligned : FvarAligned relation
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        leftPattern)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        rightPattern)) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (cospan.reifyWith left.lookupAtom? leftLeg leftPattern) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (cospan.reifyWith right.lookupAtom? rightLeg rightPattern) := by
  let leftRename := left.sourceReificationName cospan leftLeg
  let rightRename := right.sourceReificationName cospan rightLeg
  calc
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (cospan.reifyWith left.lookupAtom? leftLeg leftPattern) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (Pattern.renameFVars leftRename leftPattern) := by
      rw [left.renameFVars_sourceReificationName_eq_reifyWith cospan leftLeg]
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (Pattern.renameFVars leftRename
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              declaration leftPattern)) :=
      canonicalize_renameFVars_factor declaration quote_ne_drop leftRename
        leftPattern
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (Pattern.renameFVars rightRename
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              declaration rightPattern)) := by
      apply congrArg
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration)
      rw [left.renameFVars_sourceReificationName_eq_reifyWith cospan leftLeg,
        right.renameFVars_sourceReificationName_eq_reifyWith cospan rightLeg]
      exact cospan.reifyWith_eq_of_fvarAligned left.lookupAtom?
        right.lookupAtom? leftLeg rightLeg matched aligned
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (Pattern.renameFVars rightRename rightPattern) :=
      (canonicalize_renameFVars_factor declaration quote_ne_drop rightRename
        rightPattern).symm
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (cospan.reifyWith right.lookupAtom? rightLeg rightPattern) := by
      rw [right.renameFVars_sourceReificationName_eq_reifyWith cospan rightLeg]

namespace CostStaticAtomKeyCospan

mutual
  /-- Semantic-leaf alignment descends through common-apex reification and
  reflective supported substitution.  Each selected leaf supplies its own
  restoration equality at every binder depth; structural constructors then
  propagate those equalities, including the reflective quote reset. -/
  theorem substituteAt_reifyWith_eq_of_patternLeafAligned
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      (language : LanguageDef) (support : ContextSupport.Support)
      (assignment : ContextSupport.Assignment)
      {relation : Pattern → Pattern → Prop}
      (restores : ∀ {leftLeaf rightLeaf}, relation leftLeaf rightLeaf →
        ∀ depth,
          ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith leftResolve leftLeg leftLeaf) =
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith rightResolve rightLeg rightLeaf)) :
      ∀ {leftPattern rightPattern : Pattern},
        PatternLeafAligned relation leftPattern rightPattern →
        ∀ depth,
          ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith leftResolve leftLeg leftPattern) =
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith rightResolve rightLeg rightPattern)
    | _, _, .leaf related, depth => restores related depth
    | _, _, .bvar index, depth => by
        simp [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt]
    | _, _, .apply constructor arguments, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, List.map_map,
          Pattern.apply.injEq, true_and]
        exact substituteAt_reifyWithList_eq_of_patternLeafAlignedList cospan
          leftResolve rightResolve leftLeg rightLeg language support assignment
          restores arguments
          (if ReflectiveContextSupport.isQuoteConstructor language constructor
            then 0 else depth)
    | _, _, .lambda binder body, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, Pattern.lambda.injEq,
          true_and]
        exact substituteAt_reifyWith_eq_of_patternLeafAligned cospan
          leftResolve rightResolve leftLeg rightLeg language support assignment
          restores body (depth + 1)
    | _, _, .multiLambda arity binders body, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt,
          Pattern.multiLambda.injEq, true_and]
        exact substituteAt_reifyWith_eq_of_patternLeafAligned cospan
          leftResolve rightResolve leftLeg rightLeg language support assignment
          restores body (depth + arity)
    | _, _, .subst body replacement, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, Pattern.subst.injEq]
        exact ⟨substituteAt_reifyWith_eq_of_patternLeafAligned cospan
            leftResolve rightResolve leftLeg rightLeg language support
            assignment restores body (depth + 1),
          substituteAt_reifyWith_eq_of_patternLeafAligned cospan
            leftResolve rightResolve leftLeg rightLeg language support
            assignment restores replacement depth⟩
    | _, _, .collection collectionType rest elements, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, List.map_map,
          Pattern.collection.injEq, true_and, and_true]
        exact substituteAt_reifyWithList_eq_of_patternLeafAlignedList cospan
          leftResolve rightResolve leftLeg rightLeg language support assignment
          restores elements depth

  /-- Listwise companion of
  `substituteAt_reifyWith_eq_of_patternLeafAligned`. -/
  theorem substituteAt_reifyWithList_eq_of_patternLeafAlignedList
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      (language : LanguageDef) (support : ContextSupport.Support)
      (assignment : ContextSupport.Assignment)
      {relation : Pattern → Pattern → Prop}
      (restores : ∀ {leftLeaf rightLeaf}, relation leftLeaf rightLeaf →
        ∀ depth,
          ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith leftResolve leftLeg leftLeaf) =
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith rightResolve rightLeg rightLeaf)) :
      ∀ {leftPatterns rightPatterns : List Pattern},
        PatternLeafAlignedList relation leftPatterns rightPatterns →
        ∀ depth,
          (leftPatterns.map fun pattern =>
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith leftResolve leftLeg pattern)) =
          (rightPatterns.map fun pattern =>
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith rightResolve rightLeg pattern))
    | _, _, .nil, _ => rfl
    | _, _, .cons head tail, depth => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨substituteAt_reifyWith_eq_of_patternLeafAligned cospan
            leftResolve rightResolve leftLeg rightLeg language support
            assignment restores head depth,
          substituteAt_reifyWithList_eq_of_patternLeafAlignedList cospan
            leftResolve rightResolve leftLeg rightLeg language support
            assignment restores tail depth⟩
end

mutual
  /-- Structural free-variable alignment descends through common-apex
  reification and reflective supported substitution whenever every related
  variable pair restores equally at every possible binder depth.

  Quantifying the atomic premise over depth is essential: ordinary binders
  increase the weakening depth, while reflective quotation resets it.  The
  theorem therefore covers boundary/source-variable and boundary/boundary
  alignments without requiring their provenance-bearing semantic keys to be
  equal. -/
  theorem substituteAt_reifyWith_eq_of_fvarAligned
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      (language : LanguageDef) (support : ContextSupport.Support)
      (assignment : ContextSupport.Assignment)
      {relation : String → String → Prop}
      (restores : ∀ {leftName rightName}, relation leftName rightName →
        ∀ depth,
          ReflectiveContextSupport.substituteAt language support assignment
              depth
              (cospan.reifyWith leftResolve leftLeg (.fvar leftName)) =
            ReflectiveContextSupport.substituteAt language support assignment
              depth
              (cospan.reifyWith rightResolve rightLeg (.fvar rightName))) :
      ∀ {leftPattern rightPattern : Pattern},
        FvarAligned relation leftPattern rightPattern →
        ∀ depth,
          ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith leftResolve leftLeg leftPattern) =
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith rightResolve rightLeg rightPattern)
    | _, _, .bvar index, depth => by
        simp [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt]
    | _, _, .fvar related, depth => restores related depth
    | _, _, .apply constructor arguments, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, List.map_map,
          Pattern.apply.injEq, true_and]
        exact substituteAt_reifyWithList_eq_of_fvarAlignedList cospan
          leftResolve rightResolve leftLeg rightLeg language support assignment
          restores arguments
          (if ReflectiveContextSupport.isQuoteConstructor language constructor
            then 0 else depth)
    | _, _, .lambda binder body, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, Pattern.lambda.injEq,
          true_and]
        exact substituteAt_reifyWith_eq_of_fvarAligned cospan leftResolve
          rightResolve leftLeg rightLeg language support assignment restores
          body (depth + 1)
    | _, _, .multiLambda arity binders body, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, Pattern.multiLambda.injEq,
          true_and]
        exact substituteAt_reifyWith_eq_of_fvarAligned cospan leftResolve
          rightResolve leftLeg rightLeg language support assignment restores
          body (depth + arity)
    | _, _, .subst body replacement, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, Pattern.subst.injEq]
        exact ⟨substituteAt_reifyWith_eq_of_fvarAligned cospan leftResolve
            rightResolve leftLeg rightLeg language support assignment restores
            body (depth + 1),
          substituteAt_reifyWith_eq_of_fvarAligned cospan leftResolve
            rightResolve leftLeg rightLeg language support assignment restores
            replacement depth⟩
    | _, _, .collection collectionType rest elements, depth => by
        simp only [CostStaticAtomKeyCospan.reifyWith,
          ReflectiveContextSupport.substituteAt, List.map_map,
          Pattern.collection.injEq, true_and, and_true]
        exact substituteAt_reifyWithList_eq_of_fvarAlignedList cospan
          leftResolve rightResolve leftLeg rightLeg language support assignment
          restores elements depth

  /-- Listwise companion of
  `substituteAt_reifyWith_eq_of_fvarAligned`. -/
  theorem substituteAt_reifyWithList_eq_of_fvarAlignedList
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      (language : LanguageDef) (support : ContextSupport.Support)
      (assignment : ContextSupport.Assignment)
      {relation : String → String → Prop}
      (restores : ∀ {leftName rightName}, relation leftName rightName →
        ∀ depth,
          ReflectiveContextSupport.substituteAt language support assignment
              depth
              (cospan.reifyWith leftResolve leftLeg (.fvar leftName)) =
            ReflectiveContextSupport.substituteAt language support assignment
              depth
              (cospan.reifyWith rightResolve rightLeg (.fvar rightName))) :
      ∀ {leftPatterns rightPatterns : List Pattern},
        FvarAlignedList relation leftPatterns rightPatterns →
        ∀ depth,
          (leftPatterns.map fun pattern =>
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith leftResolve leftLeg pattern)) =
          (rightPatterns.map fun pattern =>
            ReflectiveContextSupport.substituteAt language support assignment
              depth (cospan.reifyWith rightResolve rightLeg pattern))
    | _, _, .nil, _ => rfl
    | _, _, .cons head tail, depth => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨substituteAt_reifyWith_eq_of_fvarAligned cospan leftResolve
            rightResolve leftLeg rightLeg language support assignment restores
            head depth,
          substituteAt_reifyWithList_eq_of_fvarAlignedList cospan leftResolve
            rightResolve leftLeg rightLeg language support assignment restores
            tail depth⟩
end

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
