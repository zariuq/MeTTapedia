import Mettapedia.GSLT.LanguageDef.CostRestorationLeafDichotomy
import Mettapedia.GSLT.LanguageDef.CostRestorationBoundaryVariable
import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

/-!
# When two free-variable leaves restore together

The matched-fvar callback of the root-cospan producers asks, for a pair of
reified free variables, for a `CommonRestorationApex`.  Its only route at a
leaf is `RestoresTogether`, which unfolds to one equation per depth:

```
substituteAt … depth (.fvar n) = liftBVars 0 (depth − |support n|) (assignment n)
```

So the leaf holds or fails by *arithmetic on the two assignments*, and this
module records the complete answer as kernel theorems rather than analysis:

* **joint absence** — a name carried by neither environment reifies to itself
  on both sides, and the leaf holds by reflexivity
  (`matchedFvar_apex_of_jointAbsence`);
* **joint membership with equal keys** — already in tree:
  `CostStaticAtomEnvironment.atomNames_commonRestorationApex_of_key_eq`
  routes both slots to one common key via `crossExtensional`;
* **equal assignments at equal support lengths** — the leaf holds even for
  *distinct* names (`restoresTogether_fvar_fvar_of_assignment_eq`).  In
  particular a sealed/exposed key divergence alone does **not** falsify the
  leaf while the assigned normal forms and support lengths agree;
* **distinct assignments at equal support lengths** — the leaf fails, at the
  depth where both lifts are trivial
  (`not_restoresTogether_fvar_fvar_of_assignment_ne`).

Together these settle the fate of any universally-quantified matched-fvar
callback: it is exactly as strong as "every name is jointly absent, or
jointly present with agreeing assignment arithmetic" — a property of the
*environment pair*, not of the recursion that consumes the callback.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open ReflectiveContextSupport

/-- **Distinct assignments refute the leaf.**  At `depth = |support a|` both
lifts are trivial, so the depth family forces the assignments themselves to
agree. -/
theorem not_restoresTogether_fvar_fvar_of_assignment_ne
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    {a b : String}
    (lengthEq : (support a).length = (support b).length)
    (ne : assignment a ≠ assignment b) :
    ¬ RestoresTogether profile support assignment (.fvar a) (.fvar b) := by
  intro together
  have at_support := together (support a).length
  rw [substituteAt_fvar, substituteAt_fvar, Nat.sub_self, ← lengthEq,
    Nat.sub_self, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero] at at_support
  exact ne at_support

/-- **Equal assignments at equal support lengths satisfy the leaf, even for
distinct names.**  Every depth applies the same lift to the same value.

This is the positive twin of the refutation above, and it is what survives
of the sealed/exposed configurations: diverging keys change the *names*, but
while the assigned normal forms and support lengths agree, the leaf holds. -/
theorem restoresTogether_fvar_fvar_of_assignment_eq
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    {a b : String}
    (lengthEq : (support a).length = (support b).length)
    (valueEq : assignment a = assignment b) :
    RestoresTogether profile support assignment (.fvar a) (.fvar b) := by
  intro depth
  rw [substituteAt_fvar, substituteAt_fvar, lengthEq, valueEq]

/-- **The two cospan legs reify a name identically when its atoms carry equal
keys.**

`reifyWith` touches only free variables — bound variables pass through and
every other former is structural — so two legs agree on a whole frame exactly
when they agree name by name.  Here `crossExtensional` turns key agreement
into slot agreement, and `commonAtomName` depends on nothing but the common
slot.

This is the step that repairs the naive route into the restoration lane: equal
canonicalized frames are *not* enough, because the two legs reify through
different environments; equal frames together with this agreement are. -/
theorem CostStaticAtomKeyCospan.reifyNameWith_eq_of_keys
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    (name : String)
    (agree : ∀ left right, leftResolve name = some left →
      rightResolve name = some right → leftKey left = rightKey right)
    (leftNone : leftResolve name = none → rightResolve name = none)
    (rightNone : rightResolve name = none → leftResolve name = none) :
    cospan.reifyNameWith leftResolve cospan.leftSlot name =
      cospan.reifyNameWith rightResolve cospan.rightSlot name := by
  unfold CostStaticAtomKeyCospan.reifyNameWith
  cases leftSelected : leftResolve name with
  | none =>
      rw [leftNone leftSelected]
  | some left =>
      cases rightSelected : rightResolve name with
      | none => exact absurd (rightNone rightSelected) (by simp [leftSelected])
      | some right =>
          exact congrArg cospan.commonAtomName
            ((cospan.crossExtensional left right).mpr
              (agree left right leftSelected rightSelected))

/-- **Name-level leg agreement lifts to whole patterns.**

`reifyWith` renames only free variables; every other former is structural.  So
if the two legs agree name by name — including on names neither side resolves,
where both return the name unchanged — they agree on any pattern.

Stated at the name level deliberately: a formulation demanding that *every*
name resolve on both sides is vacuous, since `lookupAtom?` decodes the name and
answers `none` off the atom namespace. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_reifyNameWith_eq
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    (names : ∀ name,
      cospan.reifyNameWith leftResolve cospan.leftSlot name =
        cospan.reifyNameWith rightResolve cospan.rightSlot name) :
    ∀ pattern,
      cospan.reifyWith leftResolve cospan.leftSlot pattern =
        cospan.reifyWith rightResolve cospan.rightSlot pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reifyWith]
  | hfvar name =>
      have nameEq := names name
      unfold CostStaticAtomKeyCospan.reifyNameWith at nameEq
      simp only [reifyWith]
      cases leftSelected : leftResolve name <;>
        cases rightSelected : rightResolve name <;> simp_all
  | happly constructor arguments inductionHypothesis =>
      simp only [reifyWith, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership
  | hlambda binder body inductionHypothesis =>
      simp only [reifyWith, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [reifyWith, Pattern.subst.injEq]
      exact ⟨bodyHypothesis, replacementHypothesis⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership

/-- **Leg agreement on the names a pattern mentions suffices for that
pattern.**

The sharper form of the lifting above: `reifyWith` renames only free
variables, so only the names actually occurring matter.  This is what makes
the statement applicable — demanding agreement at *every* string would force
the two environments to resolve identical name sets, since `lookupAtom?`
resolves exactly the atom-namespace names below `atomCount`. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_free
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount)) :
    ∀ pattern, (∀ name ∈ pattern.freeFvarNames,
        cospan.reifyNameWith leftResolve cospan.leftSlot name =
          cospan.reifyNameWith rightResolve cospan.rightSlot name) →
      cospan.reifyWith leftResolve cospan.leftSlot pattern =
        cospan.reifyWith rightResolve cospan.rightSlot pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; simp [reifyWith]
  | hfvar name =>
      intro names
      have nameEq := names name (by simp [Pattern.freeFvarNames])
      unfold CostStaticAtomKeyCospan.reifyNameWith at nameEq
      simp only [reifyWith]
      cases leftSelected : leftResolve name <;>
        cases rightSelected : rightResolve name <;> simp_all
  | happly constructor arguments inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      refine inductionHypothesis argument membership (fun name inArgument => ?_)
      exact names name (by
        simp only [Pattern.freeFvarNames, List.mem_flatMap]
        exact ⟨argument, membership, inArgument⟩)
  | hlambda binder body inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis (fun name inBody =>
        names name (by simpa [Pattern.freeFvarNames] using inBody))
  | hmultiLambda arity binders body inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis (fun name inBody =>
        names name (by simpa [Pattern.freeFvarNames] using inBody))
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro names
      simp only [reifyWith, Pattern.subst.injEq]
      refine ⟨bodyHypothesis (fun name inBody => names name ?_),
        replacementHypothesis (fun name inReplacement => names name ?_)⟩
      · simp only [Pattern.freeFvarNames, List.mem_append]
        exact .inl inBody
      · simp only [Pattern.freeFvarNames, List.mem_append]
        exact .inr inReplacement
  | hcollection collectionType elements rest inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
      apply List.map_congr_left
      intro element membership
      refine inductionHypothesis element membership (fun name inElement => ?_)
      exact names name (by
        simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
        exact .inl ⟨element, membership, inElement⟩)

/-- **Thickening ambient binders leaves the free variables alone.**

`thickenAmbientBVars` shifts de Bruijn indices and is the identity on `fvar`,
so it does not disturb the name set.  With
`StructuralMorphism.mapPattern_freeFvarNames` this lets leg agreement be
demanded on a frame's own names rather than on the reified argument's. -/
theorem CostStaticBinderThinning.thickenAmbientBVars_freeFvarNames
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound) :
    ∀ pattern depth,
      (thinning.thickenAmbientBVars depth pattern).freeFvarNames =
        pattern.freeFvarNames := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [thickenAmbientBVars, Pattern.freeFvarNames]
  | hfvar name => intro depth; simp [thickenAmbientBVars, Pattern.freeFvarNames]
  | happly constructor arguments inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames, List.flatMap_map]
      apply List.flatMap_congr
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames]
      exact inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames]
      exact inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames]
      rw [bodyHypothesis (depth + 1), replacementHypothesis depth]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames, List.flatMap_map]
      congr 1
      apply List.flatMap_congr
      intro element membership
      exact inductionHypothesis element membership depth

/-- **Reification agrees on fvar-aligned patterns whose related names reify
alike.**

The general form: the two frames need not be equal, only aligned up to names
that reify to the same thing.  That covers the case the sub-case above cannot
— two *distinct* boundary names whose atoms carry equal keys reify to one and
the same common name, so the leaf closes by reflexivity — and it also covers
names neither side resolves, which the relation may pair when identical.

`reifyNameWith_eq_of_keys` discharges the side condition from key agreement. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_fvarAligned_of_names
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    {relation : String → String → Prop}
    (names : ∀ leftName rightName, relation leftName rightName →
      cospan.reifyNameWith leftResolve cospan.leftSlot leftName =
        cospan.reifyNameWith rightResolve cospan.rightSlot rightName) :
    ∀ {leftPattern rightPattern : Pattern},
      FvarAligned relation leftPattern rightPattern →
      cospan.reifyWith leftResolve cospan.leftSlot leftPattern =
        cospan.reifyWith rightResolve cospan.rightSlot rightPattern
  | _, _, .bvar index => by simp [reifyWith]
  | _, _, .fvar related => by
      have nameEq := names _ _ related
      unfold CostStaticAtomKeyCospan.reifyNameWith at nameEq
      simp only [reifyWith]
      split <;> split <;> simp_all
  | _, _, .apply constructor arguments => by
      simp only [reifyWith, Pattern.apply.injEq, true_and]
      exact reifyWithList_eq cospan leftResolve rightResolve names arguments
  | _, _, .lambda binder body => by
      simp only [reifyWith, Pattern.lambda.injEq, true_and]
      exact reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
        rightResolve names body
  | _, _, .multiLambda arity binders body => by
      simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
      exact reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
        rightResolve names body
  | _, _, .subst body replacement => by
      simp only [reifyWith, Pattern.subst.injEq]
      exact ⟨reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
        rightResolve names body,
        reifyWith_eq_of_fvarAligned_of_names cospan leftResolve rightResolve
          names replacement⟩
  | _, _, .collection collectionType rest elements => by
      simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
      exact reifyWithList_eq cospan leftResolve rightResolve names elements
where
  reifyWithList_eq
      {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftCount))
      (rightResolve : String → Option (Fin rightCount))
      {relation : String → String → Prop}
      (names : ∀ leftName rightName, relation leftName rightName →
        cospan.reifyNameWith leftResolve cospan.leftSlot leftName =
          cospan.reifyNameWith rightResolve cospan.rightSlot rightName)
      {leftPatterns rightPatterns : List Pattern}
      (aligned : FvarAlignedList relation leftPatterns rightPatterns) :
      leftPatterns.map (cospan.reifyWith leftResolve cospan.leftSlot) =
        rightPatterns.map (cospan.reifyWith rightResolve cospan.rightSlot) :=
    match aligned with
    | .nil => rfl
    | .cons head tail => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
          rightResolve names head,
          reifyWithList_eq cospan leftResolve rightResolve names tail⟩

/-- **A non-quote application head survives keyed canonicalization.**

`canonicalizeByDepths` rewrites an application only through
`finishNormalizeReflectiveApply`, which acts at the quote constructor; every
other head is returned intact over canonicalized arguments.

This is the structural half of source-frame alignment: `CanonicalRootAligned`
carries `ne : constructor ≠ declaration.quoteConstructor` on its `apply` arm,
so two root-aligned patterns keep their shared constructor through
canonicalization and `PatternLeafAligned.apply` can fire.  The collapsing arms
are exactly the cases this excludes. -/
theorem Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_apply_of_ne_quote {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (constructor : String)
    (arguments : List Pattern)
    (notQuote : constructor ≠ declaration.quoteConstructor) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths key declaration availableDepth scopeDepth
        (.apply constructor arguments) =
      .apply constructor
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths key declaration availableDepth scopeDepth
          arguments) := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
  simp only [beq_iff_eq, notQuote, if_false]
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
  simp [notQuote]

namespace CostStaticAtomEnvironment

/-- **Joint absence closes the matched-fvar apex by reflexivity.**  A name
outside both inventories is preserved by `reifyName` on both sides and by
both positional resolvers, so the two endpoints are literally the same
pattern. -/
theorem matchedFvar_apex_of_jointAbsence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (declaration : ReflectivePresentationDecl) (depth : Nat) (name : String)
    (leftAbsent : left.slotOfName? name = none)
    (rightAbsent : right.slotOfName? name = none)
    (leftUnresolved : left.lookupAtom? name = none)
    (rightUnresolved : right.lookupAtom? name = none) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.reifyName name)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.reifyName name))) := by
  intro cospan
  have leftName : left.reifyName name = name := by
    simp [CostStaticAtomEnvironment.reifyName, leftAbsent]
  have rightName : right.reifyName name = name := by
    simp [CostStaticAtomEnvironment.reifyName, rightAbsent]
  rw [leftName, rightName]
  apply CostStaticAtomKeyCospan.CommonRestorationApex.of_eq cospan declaration
    depth
  rw [CostStaticAtomKeyCospan.reifyWith_fvar, CostStaticAtomKeyCospan.reifyWith_fvar]
  simp [CostStaticAtomKeyCospan.reifyNameWith, leftUnresolved, rightUnresolved]

/-- Joint membership with equal keys, packaged as evidence about one name.
This is the predicate a provenance theorem must attach to every matched free
variable a producer emits. -/
def MatchedFvarKeyAgreement
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (name : String) : Prop :=
  ∃ (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount),
    left.slotOfName? name = some leftSlot ∧
    right.slotOfName? name = some rightSlot ∧
    (left.atomValue leftSlot).key = (right.atomValue rightSlot).key

/-- **Key agreement closes the matched-fvar apex in `reifyName` form** — the
exact endpoint shape of the spine's remaining callback.  `reifyName` resolves
each side to its atom name, and the key-equality arm routes both to one
common key. -/
theorem matchedFvar_apex_of_keyAgreement
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (declaration : ReflectivePresentationDecl) (depth : Nat) {name : String}
    (agreement : MatchedFvarKeyAgreement left right name) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.reifyName name)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.reifyName name))) := by
  intro cospan
  obtain ⟨leftSlot, rightSlot, leftSome, rightSome, keyEq⟩ := agreement
  have leftName : left.reifyName name = left.atomName leftSlot := by
    simp [CostStaticAtomEnvironment.reifyName, leftSome]
  have rightName : right.reifyName name = right.atomName rightSlot := by
    simp [CostStaticAtomEnvironment.reifyName, rightSome]
  rw [leftName, rightName]
  exact left.atomNames_commonRestorationApex_of_key_eq right leftSlot
    rightSlot keyEq declaration depth

end CostStaticAtomEnvironment

end Mettapedia.GSLT.LanguageDef
