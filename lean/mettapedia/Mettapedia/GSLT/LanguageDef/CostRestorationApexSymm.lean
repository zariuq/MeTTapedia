import Mettapedia.GSLT.LanguageDef.CostRestorationRelationQuoteArm

/-!
# Leaf-frame transposition and depth invariance for stable assignments

Transposing a leaf-aligned frame while weakening its leaf relation is the
symmetry workhorse for paired-frame comparisons; the apex relation's own
symmetry already exists upstream and consumes exactly this shape.

Separately, supported substitution is depth-invariant whenever every
assignment value is stable under bound-variable lifting — in particular for
bound-variable-closed restored values.  This is the honest replacement for
the false generalization that every stopped cell has empty target support:
the depth quantifier in restoration premises is discharged by value
closedness, not by a support-shape claim.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

mutual
  /-- Transpose a leaf-aligned frame while weakening the leaf relation. -/
  theorem PatternLeafAligned.flip_mono
      {relation transposed : Pattern → Pattern → Prop}
      (weaken : ∀ {left right : Pattern}, relation left right →
        transposed right left) :
      ∀ {left right : Pattern},
        PatternLeafAligned relation left right →
        PatternLeafAligned transposed right left
    | _, _, .leaf related => .leaf (weaken related)
    | _, _, .bvar index => .bvar index
    | _, _, .apply constructor arguments =>
        .apply constructor
          (PatternLeafAlignedList.flip_mono weaken arguments)
    | _, _, .lambda binder body =>
        .lambda binder (PatternLeafAligned.flip_mono weaken body)
    | _, _, .multiLambda arity binders body =>
        .multiLambda arity binders (PatternLeafAligned.flip_mono weaken body)
    | _, _, .subst body replacement =>
        .subst (PatternLeafAligned.flip_mono weaken body)
          (PatternLeafAligned.flip_mono weaken replacement)
    | _, _, .collection collectionType rest elements =>
        .collection collectionType rest
          (PatternLeafAlignedList.flip_mono weaken elements)

  /-- Listwise companion of the leaf-aligned transposition. -/
  theorem PatternLeafAlignedList.flip_mono
      {relation transposed : Pattern → Pattern → Prop}
      (weaken : ∀ {left right : Pattern}, relation left right →
        transposed right left) :
      ∀ {left right : List Pattern},
        PatternLeafAlignedList relation left right →
        PatternLeafAlignedList transposed right left
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (PatternLeafAligned.flip_mono weaken head)
          (PatternLeafAlignedList.flip_mono weaken tail)
end


namespace ReflectiveContextSupport

/-- Supported substitution is depth-invariant when every assignment value is
stable under bound-variable lifting — in particular when every restored
value is bound-variable-closed.  The depth argument only reaches the
assignment through `liftBVars`, so stability makes every fvar case
depth-independent and the structural cases follow by induction. -/
theorem substituteAt_eq_of_liftStable
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (stable : ∀ name shift,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift
        (assignment name) = assignment name) :
    ∀ (pattern : Pattern) (firstDepth secondDepth : Nat),
      substituteAt profile support assignment firstDepth pattern =
        substituteAt profile support assignment secondDepth pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro firstDepth secondDepth
      simp only [substituteAt]
  | hfvar name =>
      intro firstDepth secondDepth
      simp only [substituteAt, stable]
  | happly constructor arguments ih =>
      intro firstDepth secondDepth
      simp only [substituteAt]
      refine congrArg (Pattern.apply constructor) ?_
      apply List.map_congr_left
      intro argument membership
      exact ih argument membership _ _
  | hlambda binder body ih =>
      intro firstDepth secondDepth
      simp only [substituteAt]
      exact congrArg (Pattern.lambda binder) (ih _ _)
  | hmultiLambda arity binders body ih =>
      intro firstDepth secondDepth
      simp only [substituteAt]
      exact congrArg (Pattern.multiLambda arity binders) (ih _ _)
  | hsubst body replacement ihBody ihReplacement =>
      intro firstDepth secondDepth
      simp only [substituteAt]
      exact congrArg₂ Pattern.subst (ihBody _ _) (ihReplacement _ _)
  | hcollection collectionType elements rest ih =>
      intro firstDepth secondDepth
      simp only [substituteAt]
      refine congrArg (fun mapped =>
        Pattern.collection collectionType mapped rest) ?_
      apply List.map_congr_left
      intro element membership
      exact ih element membership _ _

/-- Local form of `substituteAt_eq_of_liftStable`: only assignment values
whose names actually occur in the pattern need to be stable.  This is the
form required below a reflective quote, where the support discipline closes
every atom visible in the quoted child but unrelated atoms may retain binder
support elsewhere in the same finite environment. -/
theorem substituteAt_eq_of_liftStable_on_freeFvars
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) :
    ∀ (pattern : Pattern),
      (∀ name, name ∈ pattern.freeFvarNames → ∀ shift,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift
          (assignment name) = assignment name) →
      ∀ (firstDepth secondDepth : Nat),
        substituteAt profile support assignment firstDepth pattern =
          substituteAt profile support assignment secondDepth pattern := by
  intro pattern stable firstDepth secondDepth
  induction pattern using Pattern.inductionOn generalizing firstDepth secondDepth with
  | hbvar index =>
      simp only [substituteAt]
  | hfvar name =>
      simp only [substituteAt]
      rw [stable name (by simp [Pattern.freeFvarNames]),
        stable name (by simp [Pattern.freeFvarNames])]
  | happly constructor arguments inductionHypothesis =>
      simp only [substituteAt]
      refine congrArg (Pattern.apply constructor) ?_
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership shift
      apply stable name
      simp only [Pattern.freeFvarNames]
      exact List.mem_flatMap.mpr ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      simp only [substituteAt]
      apply congrArg (Pattern.lambda binder)
      apply inductionHypothesis
      intro name nameMembership shift
      exact stable name (by simpa only [Pattern.freeFvarNames] using nameMembership)
        shift
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [substituteAt]
      apply congrArg (Pattern.multiLambda arity binders)
      apply inductionHypothesis
      intro name nameMembership shift
      exact stable name (by simpa only [Pattern.freeFvarNames] using nameMembership)
        shift
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [substituteAt]
      apply congrArg₂ Pattern.subst
      · apply bodyHypothesis
        intro name nameMembership shift
        apply stable name
        simp [Pattern.freeFvarNames, nameMembership]
      · apply replacementHypothesis
        intro name nameMembership shift
        apply stable name
        simp [Pattern.freeFvarNames, nameMembership]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [substituteAt]
      refine congrArg (fun mapped =>
        Pattern.collection collectionType mapped rest) ?_
      apply List.map_congr_left
      intro element membership
      apply inductionHypothesis element membership
      intro name nameMembership shift
      apply stable name
      simp only [Pattern.freeFvarNames, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr ⟨element, membership, nameMembership⟩)

end ReflectiveContextSupport

namespace WellSorted.SupportedOpenAssignment

/-- An assigned open value with empty declared support is closed with respect
to de Bruijn indices, hence weakening it at the root is inert.  The result is
derived from the assignment's typing proof; it is not an extra stability law
stored in the assignment. -/
theorem liftBVars_zero_eq_self_of_support_eq_nil
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment profile language source target support)
    {name : String} {type : TypeExpr} (lookup : source name = some type)
    (supportEq : support name = []) (shift : Nat) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift
        (assignment.assignment name) = assignment.assignment name := by
  have wellScoped : (assignment.assignment name).isWellScopedAt 0 = true := by
    have typedScoped := (assignment.typed lookup).isWellScopedAt
    simpa [supportEq] using typedScoped
  exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
    wellScoped

/-- Supported restoration is independent of the ambient visible depth when
every free variable used by the pattern is a declared parameter with empty
support.  This is the exact local fact used for a payload sealed by a
reflective quote; unused parameters in the surrounding finite environment may
still retain nonempty binder support. -/
theorem substituteAt_eq_of_free_support_eq_nil
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment profile language source target support)
    (pattern : Pattern)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ type, source name = some type)
    (supportNil : ∀ name, name ∈ pattern.freeFvarNames → support name = [])
    (firstDepth secondDepth : Nat) :
    ReflectiveContextSupport.substituteAt profile support
        assignment.assignment firstDepth pattern =
      ReflectiveContextSupport.substituteAt profile support
        assignment.assignment secondDepth pattern := by
  apply ReflectiveContextSupport.substituteAt_eq_of_liftStable_on_freeFvars
  intro name membership shift
  obtain ⟨type, lookup⟩ := covered name membership
  exact assignment.liftBVars_zero_eq_self_of_support_eq_nil lookup
    (supportNil name membership) shift

end WellSorted.SupportedOpenAssignment

/-- A larger finite boundary table preserves empty restoration support for
every name typed by a smaller sealed table.  Source variables are closed by
construction; boundary variables retain the smaller table's exact entry
through the proof-relevant inclusion. -/
theorem TypedCostRegionBoundaryTable.restorationSupport_eq_nil_of_entries_subset
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (small : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (large : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (entriesSubset : small.entries ⊆ large.entries)
    (entriesSealed : ∀ boundary ∈ small.entries,
      boundary.boundary.targetSupport = [])
    {name : String} {type : TypeExpr}
    (typedName : small.sourceFreeContext name = some type) :
    large.restorationSupport name = [] := by
  cases decoded : decodeCostRegionSourceVariableName name with
  | some sourceName =>
      simp [TypedCostRegionBoundaryTable.restorationSupport, decoded]
  | none =>
      cases resolved : small.resolve name with
      | none =>
          simp [TypedCostRegionBoundaryTable.sourceFreeContext, decoded,
            resolved] at typedName
      | some boundary =>
          have membership : boundary ∈ small.entries :=
            small.mem_entries_of_resolve_eq_some resolved
          have defined : small.resolve name ≠ none := by simp [resolved]
          have largeResolved : large.resolve name = some boundary := by
            have transported :=
              small.resolve_eq_of_entries_subset large entriesSubset name
                defined
            simpa [resolved] using transported
          simp [TypedCostRegionBoundaryTable.restorationSupport, decoded,
            largeResolved, entriesSealed boundary membership]

/-- A semantic environment whose atom supports are all empty restores every
pattern independently of the ambient binder depth.  Recognized atom names are
closed by their typed empty-support fibres; unrecognized names restore to
themselves. -/
theorem CostStaticAtomEnvironment.restoreAt_eq_of_atomTargetSupport_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (supportNil : ∀ slot,
      (environment.atomValue slot).key.targetSupport = [])
    (pattern : Pattern) (firstDepth secondDepth : Nat) :
    environment.restoreAt firstDepth pattern =
      environment.restoreAt secondDepth pattern := by
  apply ReflectiveContextSupport.substituteAt_eq_of_liftStable
  intro name shift
  cases selected : environment.lookupAtom? name with
  | none =>
      simp [CostStaticAtomEnvironment.restorationAssignment, selected,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  | some slot =>
      have normalScoped :
          (environment.atomValue slot).key.normal.isWellScopedAt 0 = true := by
        have typedScoped := (environment.atomValue slot).normalTyped.isWellScopedAt
        simpa [supportNil slot] using typedScoped
      simpa [CostStaticAtomEnvironment.restorationAssignment, selected] using
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
          (shift := shift) normalScoped

/-- Restoring a pattern is independent of ambient depth when every semantic
atom name actually occurring in that pattern has empty target support.
Atoms elsewhere in the finite environment may retain nonempty support. -/
theorem CostStaticAtomEnvironment.restoreAt_eq_of_freeAtomTargetSupport_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (pattern : Pattern)
    (supportNil : ∀ name, name ∈ pattern.freeFvarNames →
      ∀ slot, environment.lookupAtom? name = some slot →
        (environment.atomValue slot).key.targetSupport = [])
    (firstDepth secondDepth : Nat) :
    environment.restoreAt firstDepth pattern =
      environment.restoreAt secondDepth pattern := by
  apply ReflectiveContextSupport.substituteAt_eq_of_liftStable_on_freeFvars
  intro name membership shift
  cases selected : environment.lookupAtom? name with
  | none =>
      simp [CostStaticAtomEnvironment.restorationAssignment, selected,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  | some slot =>
      have normalScoped :
          (environment.atomValue slot).key.normal.isWellScopedAt 0 = true := by
        have typedScoped := (environment.atomValue slot).normalTyped.isWellScopedAt
        simpa [supportNil name membership slot selected] using typedScoped
      simpa [CostStaticAtomEnvironment.restorationAssignment, selected] using
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
          (shift := shift) normalScoped

/-- The semantic ordering key is depth-independent on a frame whose used
semantic atoms all have empty target support. -/
theorem CostStaticRegionNode.semanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (pattern : Pattern)
    (supportNil : ∀ name, name ∈ pattern.freeFvarNames →
      ∀ slot, environment.lookupAtom? name = some slot →
        (environment.atomValue slot).key.targetSupport = [])
    (firstDepth secondDepth : Nat) :
    CostStaticRegionNode.semanticPatternKeyAt environment firstDepth pattern =
      CostStaticRegionNode.semanticPatternKeyAt environment secondDepth
        pattern := by
  exact congrArg Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
    (environment.restoreAt_eq_of_freeAtomTargetSupport_eq_nil pattern
      supportNil firstDepth secondDepth)

/-- Empty atom supports also make the semantic ordering key independent of
the ambient restoration depth. -/
theorem CostStaticRegionNode.semanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (supportNil : ∀ slot,
      (environment.atomValue slot).key.targetSupport = [])
    (firstDepth secondDepth : Nat) (pattern : Pattern) :
    CostStaticRegionNode.semanticPatternKeyAt environment firstDepth pattern =
      CostStaticRegionNode.semanticPatternKeyAt environment secondDepth
        pattern := by
  exact congrArg Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
    (environment.restoreAt_eq_of_atomTargetSupport_eq_nil supportNil pattern
      firstDepth secondDepth)

end Mettapedia.GSLT.LanguageDef
