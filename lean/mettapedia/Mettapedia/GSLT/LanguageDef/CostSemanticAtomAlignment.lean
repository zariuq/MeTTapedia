import Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical
import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalFreeRenaming

/-!
# Finite semantic-atom alignment

Two proof-relevant region decompositions generally have different positional
occurrence inventories.  Their evaluated atoms nevertheless share one finite
common quotient by equality of the complete typed semantic key.  The maps point
from the two positional key lists into that quotient, so the resulting object
is a cospan rather than a span.

This layer does not replace either occurrence inventory.  It only supplies the
finite semantic joint through which root-changing normalization spans can
compare evaluated meanings.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A finite common semantic quotient of two positional atom-key lists.

The three extensionality fields state that equality of quotient slots is
exactly equality of complete typed semantic keys, both within each endpoint
and across endpoints.  Thus the quotient permits duplication and coalescence
without identifying unequal fibers or normalized values. -/
structure CostStaticAtomKeyCospan
    {leftCount rightCount : Nat}
    (leftKey : Fin leftCount -> CostStaticAtomKey)
    (rightKey : Fin rightCount -> CostStaticAtomKey) where
  commonKeys : List CostStaticAtomKey
  commonNodup : commonKeys.Nodup
  leftSlot : Fin leftCount -> Fin commonKeys.length
  rightSlot : Fin rightCount -> Fin commonKeys.length
  leftCommutes : forall slot,
    commonKeys.get (leftSlot slot) = leftKey slot
  rightCommutes : forall slot,
    commonKeys.get (rightSlot slot) = rightKey slot
  leftExtensional : forall first second,
    leftSlot first = leftSlot second <->
      leftKey first = leftKey second
  rightExtensional : forall first second,
    rightSlot first = rightSlot second <->
      rightKey first = rightKey second
  crossExtensional : forall left right,
    leftSlot left = rightSlot right <->
      leftKey left = rightKey right

namespace CostStaticAtomKeyCospan

/-- Reverse the two endpoint legs of a finite semantic-atom cospan while
retaining the same common semantic quotient. -/
def symm
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    CostStaticAtomKeyCospan rightKey leftKey where
  commonKeys := cospan.commonKeys
  commonNodup := cospan.commonNodup
  leftSlot := cospan.rightSlot
  rightSlot := cospan.leftSlot
  leftCommutes := cospan.rightCommutes
  rightCommutes := cospan.leftCommutes
  leftExtensional := cospan.rightExtensional
  rightExtensional := cospan.leftExtensional
  crossExtensional := by
    intro right left
    constructor
    · intro slotsEq
      exact ((cospan.crossExtensional left right).mp slotsEq.symm).symm
    · intro keysEq
      exact ((cospan.crossExtensional left right).mpr keysEq.symm).symm

@[simp]
theorem symm_commonKeys
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    cospan.symm.commonKeys = cospan.commonKeys := rfl

@[simp]
theorem symm_leftSlot
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    cospan.symm.leftSlot = cospan.rightSlot := rfl

@[simp]
theorem symm_rightSlot
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    cospan.symm.rightSlot = cospan.leftSlot := rfl

/-- Canonical internal spelling of one slot in the common semantic quotient. -/
def commonAtomName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (slot : Fin cospan.commonKeys.length) : String :=
  costStaticAtomVariableName slot.1

/-- Common atom spellings retain the complete finite slot identity. -/
theorem commonAtomName_injective
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    Function.Injective cospan.commonAtomName := by
  intro first second equality
  apply Fin.ext
  exact costStaticAtomVariableName_injective equality

/-- Decode a common atom spelling only when its finite quotient slot is in
range. -/
def lookupCommon?
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (name : String) : Option (Fin cospan.commonKeys.length) := do
  let slot ← decodeCostStaticAtomVariableName name
  if inBounds : slot < cospan.commonKeys.length then some ⟨slot, inBounds⟩
  else none

@[simp]
theorem symm_lookupCommon?
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) (name : String) :
    cospan.symm.lookupCommon? name = cospan.lookupCommon? name := by
  cases decoded : decodeCostStaticAtomVariableName name with
  | none => simp [lookupCommon?, decoded]
  | some slot =>
      by_cases inBounds : slot < cospan.commonKeys.length
      · simp [lookupCommon?, decoded, inBounds]
      · simp [lookupCommon?, decoded, inBounds]

@[simp]
theorem lookupCommon?_commonAtomName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (slot : Fin cospan.commonKeys.length) :
    cospan.lookupCommon? (cospan.commonAtomName slot) = some slot := by
  simp [lookupCommon?, commonAtomName]

/-- Target binder support restored from the common semantic quotient. -/
def commonSupport
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    ContextSupport.Support := fun name =>
  match cospan.lookupCommon? name with
  | some slot => (cospan.commonKeys.get slot).targetSupport
  | none => []

/-- Authored source typing context of the common semantic namespace.

The common quotient stores complete keys, so its source type is intrinsic to
the slot and independent of which endpoint leg reaches it.  Names outside
the finite quotient receive no typing authority. -/
def commonSourceFreeContext
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    WellSorted.FreeTypeContext := fun name =>
  (cospan.lookupCommon? name).map fun slot =>
    (cospan.commonKeys.get slot).sourceType

@[simp]
theorem commonSourceFreeContext_commonAtomName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (slot : Fin cospan.commonKeys.length) :
    cospan.commonSourceFreeContext (cospan.commonAtomName slot) =
      some (cospan.commonKeys.get slot).sourceType := by
  simp [commonSourceFreeContext]

/-- Generated target typing context of the common semantic namespace. -/
def commonTargetFreeContext
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    WellSorted.FreeTypeContext := fun name =>
  (cospan.lookupCommon? name).map fun slot =>
    (cospan.commonKeys.get slot).targetType

@[simp]
theorem commonTargetFreeContext_commonAtomName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (slot : Fin cospan.commonKeys.length) :
    cospan.commonTargetFreeContext (cospan.commonAtomName slot) =
      some (cospan.commonKeys.get slot).targetType := by
  simp [commonTargetFreeContext]

/-- A uniform selected-colour type map carries the common source context to
the common target context exactly. -/
theorem commonSourceFreeContext_map_eq_commonTargetFreeContext
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (color : CostStaticColor)
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (typeMap : ∀ slot,
      mapTypeExpr (color.symbols source)
          (cospan.commonKeys.get slot).sourceType =
        (cospan.commonKeys.get slot).targetType) :
    cospan.commonSourceFreeContext.map (color.symbols source) =
      cospan.commonTargetFreeContext := by
  funext name
  simp only [WellSorted.FreeTypeContext.map, commonSourceFreeContext,
    commonTargetFreeContext]
  cases selected : cospan.lookupCommon? name with
  | none => simp
  | some slot => exact congrArg some (typeMap slot)

/-- Normalized compact value restored from the common semantic quotient. -/
def commonAssignment
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    ContextSupport.Assignment := fun name =>
  match cospan.lookupCommon? name with
  | some slot => (cospan.commonKeys.get slot).normal
  | none => .fvar name

@[simp]
theorem commonSupport_commonAtomName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (slot : Fin cospan.commonKeys.length) :
    cospan.commonSupport (cospan.commonAtomName slot) =
      (cospan.commonKeys.get slot).targetSupport := by
  simp [commonSupport]

@[simp]
theorem commonAssignment_commonAtomName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (slot : Fin cospan.commonKeys.length) :
    cospan.commonAssignment (cospan.commonAtomName slot) =
      (cospan.commonKeys.get slot).normal := by
  simp [commonAssignment]

/-- Reify one left endpoint name through its positional resolver into the
common semantic namespace.  Names outside the endpoint inventory are
preserved. -/
def reifyLeftName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin leftCount)) (name : String) : String :=
  match resolve name with
  | some slot => cospan.commonAtomName (cospan.leftSlot slot)
  | none => name

/-- Right-endpoint companion to `reifyLeftName`. -/
def reifyRightName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin rightCount)) (name : String) : String :=
  match resolve name with
  | some slot => cospan.commonAtomName (cospan.rightSlot slot)
  | none => name

/-- Structurally reify one endpoint frame through a chosen leg of the common
semantic quotient.  Only free parameter names change; constructors, bound
indices, binder metadata, and collection tails remain untouched. -/
def reifyWith
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length) :
    Pattern -> Pattern
  | .bvar index => .bvar index
  | .fvar name =>
      match resolve name with
      | some slot => .fvar (cospan.commonAtomName (leg slot))
      | none => .fvar name
  | .apply constructor arguments =>
      .apply constructor (arguments.map (cospan.reifyWith resolve leg))
  | .lambda binder body =>
      .lambda binder (cospan.reifyWith resolve leg body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders (cospan.reifyWith resolve leg body)
  | .subst body replacement =>
      .subst (cospan.reifyWith resolve leg body)
        (cospan.reifyWith resolve leg replacement)
  | .collection collectionType elements rest =>
      .collection collectionType
        (elements.map (cospan.reifyWith resolve leg)) rest
termination_by pattern => sizeOf pattern

/-- Reversing a cospan does not change reification through a fixed leg: the
common semantic quotient and its internal atom names are retained exactly. -/
theorem symm_reifyWith
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length) :
    forall pattern,
      cospan.symm.reifyWith resolve leg pattern =
        cospan.reifyWith resolve leg pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reifyWith]
  | hfvar name =>
      cases resolve name <;>
        simp [reifyWith, CostStaticAtomKeyCospan.symm, commonAtomName]
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

@[simp]
theorem symm_commonSupport
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    cospan.symm.commonSupport = cospan.commonSupport := by
  funext name
  unfold commonSupport lookupCommon? CostStaticAtomKeyCospan.symm
  cases decoded : decodeCostStaticAtomVariableName name with
  | none => simp
  | some slot =>
      by_cases inBounds : slot < cospan.commonKeys.length
      · simp [inBounds]
      · simp [inBounds]

@[simp]
theorem symm_commonAssignment
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey) :
    cospan.symm.commonAssignment = cospan.commonAssignment := by
  funext name
  unfold commonAssignment lookupCommon? CostStaticAtomKeyCospan.symm
  cases decoded : decodeCostStaticAtomVariableName name with
  | none => simp
  | some slot =>
      by_cases inBounds : slot < cospan.commonKeys.length
      · simp [inBounds]
      · simp [inBounds]

/-- Semantic-atom reification commutes with the local quote/drop contraction.
Only free-variable spellings change, so the reflective constructor test and
the contracted payload are preserved exactly. -/
theorem reifyWith_finishNormalizeReflectiveApply
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    cospan.reifyWith resolve leg
        (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration constructor arguments) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration constructor
        (arguments.map (cospan.reifyWith resolve leg)) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution in
    by_cases isQuote : constructor = declaration.quoteConstructor
    · subst constructor
      cases arguments with
      | nil => simp [finishNormalizeReflectiveApply, reifyWith]
      | cons argument arguments =>
          cases arguments with
          | cons second remainder =>
              simp [finishNormalizeReflectiveApply, reifyWith]
          | nil =>
              cases argument with
              | bvar index => simp [finishNormalizeReflectiveApply, reifyWith]
              | fvar name =>
                  cases selected : resolve name <;>
                    simp [finishNormalizeReflectiveApply, reifyWith, selected]
              | apply nestedConstructor nestedArguments =>
                  cases nestedArguments with
                  | nil => simp [finishNormalizeReflectiveApply, reifyWith]
                  | cons name tail =>
                      cases tail with
                      | cons second remainder =>
                          simp [finishNormalizeReflectiveApply, reifyWith]
                      | nil =>
                          by_cases isDrop :
                              nestedConstructor = declaration.dropConstructor
                          · subst nestedConstructor
                            simp [finishNormalizeReflectiveApply, reifyWith]
                          · simp [finishNormalizeReflectiveApply, reifyWith,
                              isDrop]
              | lambda binder body =>
                  simp [finishNormalizeReflectiveApply, reifyWith]
              | multiLambda arity binders body =>
                  simp [finishNormalizeReflectiveApply, reifyWith]
              | subst body replacement =>
                  simp [finishNormalizeReflectiveApply, reifyWith]
              | collection collectionType elements rest =>
                  simp [finishNormalizeReflectiveApply, reifyWith]
    · simp [finishNormalizeReflectiveApply, reifyWith, isQuote]

/-- Reification cannot manufacture or erase a nullary constructor. -/
theorem reifyWith_eq_apply_nil_iff
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (pattern : Pattern) (constructor : String) :
    cospan.reifyWith resolve leg pattern = .apply constructor [] <->
      pattern = .apply constructor [] := by
  cases pattern with
  | bvar index => simp [reifyWith]
  | fvar name =>
      cases selected : resolve name <;> simp [reifyWith, selected]
  | apply label arguments => simp [reifyWith]
  | lambda binder body => simp [reifyWith]
  | multiLambda arity binders body => simp [reifyWith]
  | subst body replacement => simp [reifyWith]
  | collection collectionType elements rest => simp [reifyWith]

/-- Semantic-atom reification commutes with one-layer parallel splicing. -/
theorem reifyWith_parallelSplice
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration
        pattern).map (cospan.reifyWith resolve leg) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration
        (cospan.reifyWith resolve leg pattern) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    cases pattern with
    | bvar index => simp [parallelSplice, reifyWith]
    | fvar name =>
        cases selected : resolve name <;>
          simp [parallelSplice, reifyWith, selected]
    | apply constructor arguments => simp [parallelSplice, reifyWith]
    | lambda binder body => simp [parallelSplice, reifyWith]
    | multiLambda arity binders body => simp [parallelSplice, reifyWith]
    | subst body replacement => simp [parallelSplice, reifyWith]
    | collection collectionType elements rest =>
        cases rest with
        | some restName => simp [parallelSplice, reifyWith]
        | none =>
            simp only [parallelSplice, reifyWith]
            by_cases isParallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              simp
            · have notParallelBool :
                  (collectionType == declaration.parallelCollection) = false :=
                beq_eq_false_iff_ne.mpr isParallel
              simp [notParallelBool, reifyWith]

/-- Deleting the selected parallel unit commutes with semantic-atom
reification. -/
theorem reifyWith_filter_ne_parallelUnit
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (constructor : String) : forall patterns : List Pattern,
    (patterns.filter fun pattern => pattern ≠ .apply constructor []).map
        (cospan.reifyWith resolve leg) =
      (patterns.map (cospan.reifyWith resolve leg)).filter fun pattern =>
        pattern ≠ .apply constructor []
  | [] => rfl
  | pattern :: patterns => by
      by_cases isUnit : pattern = .apply constructor []
      · subst pattern
        simpa [reifyWith] using
          reifyWith_filter_ne_parallelUnit cospan resolve leg constructor
            patterns
      · have reifiedNotUnit :
            cospan.reifyWith resolve leg pattern ≠ .apply constructor [] :=
          fun equality => isUnit
            ((cospan.reifyWith_eq_apply_nil_iff resolve leg pattern constructor).mp
              equality)
        simpa [isUnit, reifiedNotUnit] using congrArg
          (List.cons (cospan.reifyWith resolve leg pattern))
          (reifyWith_filter_ne_parallelUnit cospan resolve leg constructor
            patterns)

/-- Unsorted parallel contents commute with semantic-atom reification. -/
theorem reifyWith_parallelContents
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        patterns).map (cospan.reifyWith resolve leg) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        (patterns.map (cospan.reifyWith resolve leg)) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    unfold parallelContents
    rw [reifyWith_filter_ne_parallelUnit]
    rw [List.map_flatMap, List.flatMap_map]
    apply congrArg
    apply List.flatMap_congr
    intro pattern membership
    exact cospan.reifyWith_parallelSplice resolve leg declaration pattern

/-- Keyed parallel normalization is natural under atom reification when the
source key is the pullback of the common semantic key. -/
theorem reifyWith_normalizeParallelElementsBy
    {Key : Type} [LinearOrder Key]
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (key : Pattern -> Key) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (fun pattern => key (cospan.reifyWith resolve leg pattern)) declaration
        patterns).map (cospan.reifyWith resolve leg) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        key declaration (patterns.map (cospan.reifyWith resolve leg)) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    unfold normalizeParallelElementsBy
    rw [CostHereditaryCanonical.map_sortPatternsBy]
    exact congrArg
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key)
      (cospan.reifyWith_parallelContents resolve leg declaration patterns)

/-- Rebuilding the normalized parallel node commutes with semantic-atom
reification. -/
theorem reifyWith_collapseParallel
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    cospan.reifyWith resolve leg
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration patterns) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
        (patterns.map (cospan.reifyWith resolve leg)) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    cases patterns with
    | nil => simp [collapseParallel, reifyWith]
    | cons first remaining =>
        cases remaining with
        | nil => rfl
        | cons second tail => simp [collapseParallel, reifyWith]

/-- Two-depth keyed canonicalization is strictly natural under semantic-atom
reification when the endpoint key is the pullback of the common semantic key.
This is the generic replacement for endpoint-specific ordering calculations. -/
theorem reifyWith_canonicalizeByDepths
    {Key : Type} [LinearOrder Key]
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (key : Nat -> Nat -> Pattern -> Key)
    (declaration : ReflectivePresentationDecl) :
    forall availableDepth scopeDepth pattern,
      cospan.reifyWith resolve leg
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
            (fun availableDepth scopeDepth pattern =>
              key availableDepth scopeDepth
                (cospan.reifyWith resolve leg pattern))
            declaration availableDepth scopeDepth pattern) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths key
          declaration availableDepth scopeDepth
          (cospan.reifyWith resolve leg pattern) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    intro availableDepth scopeDepth pattern
    induction pattern using Pattern.inductionOn generalizing availableDepth
        scopeDepth with
    | hbvar index => simp [canonicalizeByDepths, reifyWith]
    | hfvar name =>
        cases selected : resolve name <;>
          simp [canonicalizeByDepths, reifyWith, selected]
    | happly constructor arguments inductionHypothesis =>
        let childAvailableDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        have listFactor :
            (canonicalizeListByDepths
                (fun availableDepth scopeDepth pattern =>
                  key availableDepth scopeDepth
                    (cospan.reifyWith resolve leg pattern))
                declaration childAvailableDepth scopeDepth arguments).map
                (cospan.reifyWith resolve leg) =
              canonicalizeListByDepths key declaration childAvailableDepth
                scopeDepth
                (arguments.map (cospan.reifyWith resolve leg)) := by
          rw [canonicalizeListByDepths_eq_map,
            canonicalizeListByDepths_eq_map]
          simp only [List.map_map]
          apply List.map_congr_left
          intro argument membership
          exact inductionHypothesis argument membership childAvailableDepth
            scopeDepth
        simp only [canonicalizeByDepths, reifyWith]
        change cospan.reifyWith resolve leg
            (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration constructor
              (canonicalizeListByDepths
                (fun availableDepth scopeDepth pattern =>
                  key availableDepth scopeDepth
                    (cospan.reifyWith resolve leg pattern))
                declaration childAvailableDepth scopeDepth arguments)) = _
        rw [cospan.reifyWith_finishNormalizeReflectiveApply, listFactor]
    | hlambda binder body inductionHypothesis =>
        simp only [canonicalizeByDepths, reifyWith, Pattern.lambda.injEq,
          true_and]
        exact inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
    | hmultiLambda arity binders body inductionHypothesis =>
        simp only [canonicalizeByDepths, reifyWith,
          Pattern.multiLambda.injEq, true_and]
        exact inductionHypothesis (availableDepth + arity)
          (scopeDepth + arity)
    | hsubst body replacement bodyInduction replacementInduction =>
        simp only [canonicalizeByDepths, reifyWith, Pattern.subst.injEq]
        exact ⟨bodyInduction (availableDepth + 1) (scopeDepth + 1),
          replacementInduction availableDepth scopeDepth⟩
    | hcollection collectionType elements rest inductionHypothesis =>
        have listFactor :
            (canonicalizeListByDepths
                (fun availableDepth scopeDepth pattern =>
                  key availableDepth scopeDepth
                    (cospan.reifyWith resolve leg pattern))
                declaration availableDepth scopeDepth elements).map
                (cospan.reifyWith resolve leg) =
              canonicalizeListByDepths key declaration availableDepth
                scopeDepth
                (elements.map (cospan.reifyWith resolve leg)) := by
          rw [canonicalizeListByDepths_eq_map,
            canonicalizeListByDepths_eq_map]
          simp only [List.map_map]
          apply List.map_congr_left
          intro element membership
          exact inductionHypothesis element membership availableDepth scopeDepth
        cases rest with
        | some restName =>
            simp only [canonicalizeByDepths, reifyWith,
              Pattern.collection.injEq, true_and]
            exact ⟨listFactor, trivial⟩
        | none =>
            by_cases isParallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              simp only [canonicalizeByDepths, reifyWith,
                beq_self_eq_true, if_true]
              rw [cospan.reifyWith_collapseParallel]
              rw [cospan.reifyWith_normalizeParallelElementsBy, listFactor]
            · have notParallel :
                  (collectionType == declaration.parallelCollection) = false :=
                beq_eq_false_iff_ne.mpr isParallel
              simpa [canonicalizeByDepths, reifyWith, notParallel, isParallel]
                using congrArg
                  (fun normalizedElements =>
                    Pattern.collection collectionType normalizedElements none)
                  listFactor

/-- Stable semantic-key sorting depends only on the values of the key on the
finite input list.  This local form is stronger than global function
extensionality and is the appropriate interface for proof-relevant atom
frames, whose ordering key is defined only on their covered names. -/
theorem sortPatternsBy_eq_of_keys_eq_on
    {Key : Type} [LinearOrder Key] (leftKey rightKey : Pattern -> Key)
    (patterns : List Pattern)
    (keysAgree : forall pattern, pattern ∈ patterns ->
      leftKey pattern = rightKey pattern) :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy leftKey patterns =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy rightKey patterns := by
  unfold Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
  have comparisonAgree : forall left, left ∈ patterns ->
      forall right, right ∈ patterns ->
        decide (leftKey left <= leftKey right) =
          decide (rightKey left <= rightKey right) := by
    intro left leftMembership right rightMembership
    rw [keysAgree left leftMembership, keysAgree right rightMembership]
  simpa using
    (List.map_mergeSort (f := id) comparisonAgree)

/-- Keyed parallel normalization preserves aggregate free-variable support.
The semantic key changes only stable order; flattening and unit deletion are
the authored reflective operations already covered by `parallelContents`. -/
theorem mem_flatMap_freeFvarNames_normalizeParallelElementsBy_iff
    {Key : Type} [LinearOrder Key] (key : Pattern -> Key)
    (declaration : ReflectivePresentationDecl) (name : String)
    (patterns : List Pattern) :
    name ∈ (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        key declaration patterns).flatMap Pattern.freeFvarNames <->
      name ∈ patterns.flatMap Pattern.freeFvarNames := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    unfold normalizeParallelElementsBy
  have permutation :=
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration patterns)).flatMap_right Pattern.freeFvarNames
  exact permutation.mem_iff.trans
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_flatMap_freeFvarNames_parallelContents_iff
      declaration name patterns)

/-- Two-depth keyed canonicalization preserves exactly the set of free names.
This support law is independent of the ordering key and makes atom coverage a
stable carrier for canonicalization. -/
theorem mem_freeFvarNames_canonicalizeByDepths_iff
    {Key : Type} [LinearOrder Key]
    (key : Nat -> Nat -> Pattern -> Key)
    (declaration : ReflectivePresentationDecl) (name : String) :
    forall availableDepth scopeDepth pattern,
      name ∈
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
            key declaration availableDepth scopeDepth pattern).freeFvarNames
        <-> name ∈ pattern.freeFvarNames := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    intro availableDepth scopeDepth pattern
    induction pattern using Pattern.inductionOn generalizing availableDepth
        scopeDepth with
    | hbvar index => simp [canonicalizeByDepths, Pattern.freeFvarNames]
    | hfvar variableName =>
        simp [canonicalizeByDepths, Pattern.freeFvarNames]
    | happly constructor arguments inductionHypothesis =>
        have listSupport :
            name ∈ (canonicalizeListByDepths key declaration
                (if constructor == declaration.quoteConstructor then 0
                  else availableDepth)
                scopeDepth arguments).flatMap Pattern.freeFvarNames <->
              name ∈ arguments.flatMap Pattern.freeFvarNames := by
          rw [canonicalizeListByDepths_eq_map]
          simp only [List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨normalized, ⟨argument, membership, rfl⟩, support⟩
            exact ⟨argument, membership,
              (inductionHypothesis argument membership _ _).mp support⟩
          · rintro ⟨argument, membership, support⟩
            exact ⟨canonicalizeByDepths key declaration
                (if constructor == declaration.quoteConstructor then 0
                  else availableDepth) scopeDepth argument,
              ⟨argument, membership, rfl⟩,
              (inductionHypothesis argument membership _ _).mpr support⟩
        simp only [canonicalizeByDepths]
        rw [mem_freeFvarNames_finishNormalizeReflectiveApply_iff]
        simpa [Pattern.freeFvarNames] using listSupport
    | hlambda binderName body inductionHypothesis =>
        simpa [canonicalizeByDepths, Pattern.freeFvarNames] using
          inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
    | hmultiLambda arity binderNames body inductionHypothesis =>
        simpa [canonicalizeByDepths, Pattern.freeFvarNames] using
          inductionHypothesis (availableDepth + arity) (scopeDepth + arity)
    | hsubst body replacement bodyInduction replacementInduction =>
        simp [canonicalizeByDepths, Pattern.freeFvarNames,
          bodyInduction (availableDepth + 1) (scopeDepth + 1),
          replacementInduction availableDepth scopeDepth]
    | hcollection collectionType elements rest inductionHypothesis =>
        have listSupport :
            name ∈ (canonicalizeListByDepths key declaration availableDepth
                scopeDepth elements).flatMap Pattern.freeFvarNames <->
              name ∈ elements.flatMap Pattern.freeFvarNames := by
          rw [canonicalizeListByDepths_eq_map]
          simp only [List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨normalized, ⟨element, membership, rfl⟩, support⟩
            exact ⟨element, membership,
              (inductionHypothesis element membership _ _).mp support⟩
          · rintro ⟨element, membership, support⟩
            exact ⟨canonicalizeByDepths key declaration availableDepth
                scopeDepth element, ⟨element, membership, rfl⟩,
              (inductionHypothesis element membership _ _).mpr support⟩
        cases rest with
        | some restName =>
            simp [canonicalizeByDepths, Pattern.freeFvarNames, listSupport]
        | none =>
            by_cases selected :
                collectionType = declaration.parallelCollection
            · subst collectionType
              simp only [canonicalizeByDepths, beq_self_eq_true, if_true]
              rw [mem_freeFvarNames_collapseParallel_iff,
                mem_flatMap_freeFvarNames_normalizeParallelElementsBy_iff]
              simpa [Pattern.freeFvarNames] using listSupport
            · have selectedFalse :
                  (collectionType == declaration.parallelCollection) = false :=
                beq_eq_false_iff_ne.mpr selected
              simp [canonicalizeByDepths, Pattern.freeFvarNames,
                selectedFalse, listSupport]

/-- Left endpoint frame in the common semantic namespace. -/
def reifyLeft
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin leftCount)) (pattern : Pattern) : Pattern :=
  cospan.reifyWith resolve cospan.leftSlot pattern

/-- Right endpoint frame in the common semantic namespace. -/
def reifyRight
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin rightCount)) (pattern : Pattern) : Pattern :=
  cospan.reifyWith resolve cospan.rightSlot pattern

/-- Free-parameter reification commutes with every structural presentation
symbol map.  Constructor colouring and semantic-atom naming therefore remain
independent operations. -/
theorem reifyWith_mapPattern
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    cospan.reifyWith resolve leg (mapPattern symbols pattern) =
      mapPattern symbols (cospan.reifyWith resolve leg pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, reifyWith]
  | hfvar name =>
      cases selected : resolve name <;> simp [mapPattern, reifyWith, selected]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, reifyWith, List.map_map,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership
  | hlambda binder body inductionHypothesis =>
      simp [mapPattern, reifyWith, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [mapPattern, reifyWith, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [mapPattern, reifyWith, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, reifyWith, List.map_map,
        Pattern.collection.injEq, true_and]
      exact ⟨List.map_congr_left fun element membership =>
        inductionHypothesis element membership, trivial⟩

/-- Common semantic-atom reification commutes with ambient-binder
reinsertion.  The two operations act on disjoint coordinates of the shared
pattern carrier: endpoint reification changes free names, while thinning
changes only de Bruijn indices. -/
@[simp]
theorem reifyWith_thickenAmbientBVars
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (pattern : Pattern) :
    cospan.reifyWith resolve leg
        (thinning.thickenAmbientBVars depth pattern) =
      thinning.thickenAmbientBVars depth
        (cospan.reifyWith resolve leg pattern) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reifyWith]
  | hfvar name =>
      cases selected : resolve name <;>
        simp [CostStaticBinderThinning.thickenAmbientBVars, reifyWith,
          selected]
  | happly constructor arguments inductionHypothesis =>
      simp only [CostStaticBinderThinning.thickenAmbientBVars, reifyWith,
        List.map_map, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reifyWith,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reifyWith,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reifyWith,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [CostStaticBinderThinning.thickenAmbientBVars, reifyWith,
        List.map_map, Pattern.collection.injEq, true_and]
      exact ⟨List.map_congr_left (fun element membership =>
        inductionHypothesis element membership depth), trivial⟩

/-- Reification commutes with the complete source-to-static target action on
a raw plan slice: first map the source symbols, then reinsert the target-only
ambient binders. -/
theorem reifyWith_mappedThickened
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin endpointCount))
    (leg : Fin endpointCount -> Fin cospan.commonKeys.length)
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (pattern : Pattern) :
    cospan.reifyWith resolve leg
        (thinning.thickenAmbientBVars depth
          (mapPattern (color.symbols source) pattern)) =
      thinning.thickenAmbientBVars depth
        (mapPattern (color.symbols source)
          (cospan.reifyWith resolve leg pattern)) := by
  rw [cospan.reifyWith_thickenAmbientBVars resolve leg thinning,
    cospan.reifyWith_mapPattern]

/-- Independently sourced endpoint names receive the same common atom
spelling whenever their selected positional atoms have the same complete
typed semantic key. -/
theorem reifyLeftName_eq_reifyRightName_of_key_eq
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String -> Option (Fin leftCount))
    (rightResolve : String -> Option (Fin rightCount))
    {leftName rightName : String} {leftSlot : Fin leftCount}
    {rightSlot : Fin rightCount}
    (leftSelected : leftResolve leftName = some leftSlot)
    (rightSelected : rightResolve rightName = some rightSlot)
    (keyEquality : leftKey leftSlot = rightKey rightSlot) :
    cospan.reifyLeftName leftResolve leftName =
      cospan.reifyRightName rightResolve rightName := by
  simp only [reifyLeftName, reifyRightName, leftSelected, rightSelected]
  exact congrArg cospan.commonAtomName
    ((cospan.crossExtensional leftSlot rightSlot).mpr keyEquality)

/-- Restoring a successfully selected left endpoint name through the common
quotient yields exactly that endpoint atom's normalized value. -/
theorem commonAssignment_reifyLeftName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin leftCount))
    {name : String} {slot : Fin leftCount}
    (selected : resolve name = some slot) :
    cospan.commonAssignment (cospan.reifyLeftName resolve name) =
      (leftKey slot).normal := by
  simp only [reifyLeftName, selected,
    cospan.commonAssignment_commonAtomName]
  exact congrArg CostStaticAtomKey.normal (cospan.leftCommutes slot)

/-- Left endpoint target support is restored exactly through the common
quotient. -/
theorem commonSupport_reifyLeftName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin leftCount))
    {name : String} {slot : Fin leftCount}
    (selected : resolve name = some slot) :
    cospan.commonSupport (cospan.reifyLeftName resolve name) =
      (leftKey slot).targetSupport := by
  simp only [reifyLeftName, selected, cospan.commonSupport_commonAtomName]
  exact congrArg CostStaticAtomKey.targetSupport (cospan.leftCommutes slot)

/-- Right endpoint value companion to `commonAssignment_reifyLeftName`. -/
theorem commonAssignment_reifyRightName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin rightCount))
    {name : String} {slot : Fin rightCount}
    (selected : resolve name = some slot) :
    cospan.commonAssignment (cospan.reifyRightName resolve name) =
      (rightKey slot).normal := by
  simp only [reifyRightName, selected,
    cospan.commonAssignment_commonAtomName]
  exact congrArg CostStaticAtomKey.normal (cospan.rightCommutes slot)

/-- Right endpoint target-support companion. -/
theorem commonSupport_reifyRightName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String -> Option (Fin rightCount))
    {name : String} {slot : Fin rightCount}
    (selected : resolve name = some slot) :
    cospan.commonSupport (cospan.reifyRightName resolve name) =
      (rightKey slot).targetSupport := by
  simp only [reifyRightName, selected, cospan.commonSupport_commonAtomName]
  exact congrArg CostStaticAtomKey.targetSupport (cospan.rightCommutes slot)

/-- Conversely, equality of two successfully reified endpoint names exposes
equality of their complete typed semantic keys. -/
theorem key_eq_of_reifyLeftName_eq_reifyRightName
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String -> Option (Fin leftCount))
    (rightResolve : String -> Option (Fin rightCount))
    {leftName rightName : String} {leftSlot : Fin leftCount}
    {rightSlot : Fin rightCount}
    (leftSelected : leftResolve leftName = some leftSlot)
    (rightSelected : rightResolve rightName = some rightSlot)
    (nameEquality : cospan.reifyLeftName leftResolve leftName =
      cospan.reifyRightName rightResolve rightName) :
    leftKey leftSlot = rightKey rightSlot := by
  simp only [reifyLeftName, reifyRightName, leftSelected, rightSelected]
    at nameEquality
  exact (cospan.crossExtensional leftSlot rightSlot).mp
    (cospan.commonAtomName_injective nameEquality)

/-- The canonical executable common quotient is the duplicate-free union of
the two finite semantic-key lists. -/
def ofFunctions {leftCount rightCount : Nat}
    (leftKey : Fin leftCount -> CostStaticAtomKey)
    (rightKey : Fin rightCount -> CostStaticAtomKey) :
    CostStaticAtomKeyCospan leftKey rightKey where
  commonKeys := (List.ofFn leftKey ++ List.ofFn rightKey).dedup
  commonNodup := List.nodup_dedup _
  leftSlot := fun slot =>
    let membership : leftKey slot ∈
        (List.ofFn leftKey ++ List.ofFn rightKey).dedup := by
      simp
    ⟨List.idxOf (leftKey slot)
        (List.ofFn leftKey ++ List.ofFn rightKey).dedup,
      List.idxOf_lt_length_of_mem membership⟩
  rightSlot := fun slot =>
    let membership : rightKey slot ∈
        (List.ofFn leftKey ++ List.ofFn rightKey).dedup := by
      simp
    ⟨List.idxOf (rightKey slot)
        (List.ofFn leftKey ++ List.ofFn rightKey).dedup,
      List.idxOf_lt_length_of_mem membership⟩
  leftCommutes := by
    intro slot
    exact List.idxOf_get
      (List.idxOf_lt_length_of_mem (by simp :
        leftKey slot ∈
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup))
  rightCommutes := by
    intro slot
    exact List.idxOf_get
      (List.idxOf_lt_length_of_mem (by simp :
        rightKey slot ∈
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup))
  leftExtensional := by
    intro first second
    constructor
    · intro equalSlot
      have equalValue := congrArg
        (fun slot => (List.ofFn leftKey ++
          List.ofFn rightKey).dedup.get slot) equalSlot
      simpa only [List.idxOf_get] using equalValue
    · intro equalValue
      apply Fin.ext
      change List.idxOf (leftKey first)
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup =
        List.idxOf (leftKey second)
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup
      rw [equalValue]
  rightExtensional := by
    intro first second
    constructor
    · intro equalSlot
      have equalValue := congrArg
        (fun slot => (List.ofFn leftKey ++
          List.ofFn rightKey).dedup.get slot) equalSlot
      simpa only [List.idxOf_get] using equalValue
    · intro equalValue
      apply Fin.ext
      change List.idxOf (rightKey first)
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup =
        List.idxOf (rightKey second)
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup
      rw [equalValue]
  crossExtensional := by
    intro left right
    constructor
    · intro equalSlot
      have equalValue := congrArg
        (fun slot => (List.ofFn leftKey ++
          List.ofFn rightKey).dedup.get slot) equalSlot
      simpa only [List.idxOf_get] using equalValue
    · intro equalValue
      apply Fin.ext
      change List.idxOf (leftKey left)
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup =
        List.idxOf (rightKey right)
          (List.ofFn leftKey ++ List.ofFn rightKey).dedup
      rw [equalValue]

@[simp]
theorem ofFunctions_commonKeys {leftCount rightCount : Nat}
    (leftKey : Fin leftCount -> CostStaticAtomKey)
    (rightKey : Fin rightCount -> CostStaticAtomKey) :
    (ofFunctions leftKey rightKey).commonKeys =
      (List.ofFn leftKey ++ List.ofFn rightKey).dedup :=
  rfl

/-- The canonical duplicate-free union contains no atom without endpoint
provenance. -/
theorem ofFunctions_has_endpoint_origin
    {leftCount rightCount : Nat}
    (leftKey : Fin leftCount -> CostStaticAtomKey)
    (rightKey : Fin rightCount -> CostStaticAtomKey)
    (slot : Fin (ofFunctions leftKey rightKey).commonKeys.length) :
    (∃ left, (ofFunctions leftKey rightKey).commonKeys.get slot =
        leftKey left) ∨
      ∃ right, (ofFunctions leftKey rightKey).commonKeys.get slot =
        rightKey right := by
  have membership : (ofFunctions leftKey rightKey).commonKeys.get slot ∈
      List.ofFn leftKey ++ List.ofFn rightKey := by
    apply List.mem_dedup.mp
    simpa only [ofFunctions_commonKeys] using List.get_mem _ slot
  rcases List.mem_append.mp membership with leftMembership | rightMembership
  · left
    obtain ⟨left, equality⟩ := List.mem_ofFn.mp leftMembership
    exact ⟨left, equality.symm⟩
  · right
    obtain ⟨right, equality⟩ := List.mem_ofFn.mp rightMembership
    exact ⟨right, equality.symm⟩

/-- Semantic ordering key at the common cospan apex.  It restores common
atoms through their complete target support and normalized value before
computing the collision-free compact-pattern code. -/
def commonSemanticPatternKeyAt
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (pattern : Pattern) : Nat :=
  Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
    (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment availableDepth pattern)

/-- Equality of common semantic keys is exactly equality after restoration at
the indexed binder depth.  The result relies on the independently proved
injectivity of compact pattern codes; the key is not merely a hash. -/
theorem commonSemanticPatternKeyAt_eq_iff
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (left right : Pattern) :
    cospan.commonSemanticPatternKeyAt source availableDepth left =
        cospan.commonSemanticPatternKeyAt source availableDepth right ↔
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment availableDepth left =
        ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment availableDepth right := by
  constructor
  · intro equal
    apply Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode_injective
    exact equal
  · intro equal
    exact congrArg Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode equal

/-- Sorting opaque common-apex atoms by their restored compact meanings and
then restoring is exactly ordinary collision-free sorting of those meanings.

This is deliberately a one-layer statement: normalized atom values remain
opaque and are not recursively canonicalized by the surrounding region. -/
theorem map_sortPatternsBy_commonSemanticPatternKeyAt
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (patterns : List Pattern) :
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (cospan.commonSemanticPatternKeyAt source availableDepth)
        patterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth) =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
        (patterns.map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment
            availableDepth)) := by
  change
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (fun pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth
            pattern)) patterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth) = _
  simpa using
    (CostHereditaryCanonical.map_sortPatternsBy
      (f := ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth)
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode patterns)

/-- The parallel layer of semantic-atom normalization depends only on the
multiset of restored outer contents.  In particular, it cannot observe the
proof-relevant spelling or origin of an opaque foreign child. -/
theorem map_normalizeParallelElementsBy_commonSemanticPatternKeyAt
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt source availableDepth)
        declaration patterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth) =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
          declaration patterns).map
            (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
              cospan.commonSupport cospan.commonAssignment
              availableDepth)) := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
  exact cospan.map_sortPatternsBy_commonSemanticPatternKeyAt source
    availableDepth
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
      patterns)

/-- Foreign parallel rearrangement is observationally harmless whenever the
restored outer contents present the same multiset.  This is the exact quotient
law needed by the rho generated-occurrence classifier. -/
theorem map_normalizeParallelElementsBy_commonSemanticPatternKeyAt_eq_of_perm
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl)
    {leftPatterns rightPatterns : List Pattern}
    (permutation : List.Perm
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration leftPatterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration rightPatterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth))) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt source availableDepth)
        declaration leftPatterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth) =
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt source availableDepth)
        declaration rightPatterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth) := by
  rw [cospan.map_normalizeParallelElementsBy_commonSemanticPatternKeyAt source,
    cospan.map_normalizeParallelElementsBy_commonSemanticPatternKeyAt source]
  exact Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns_eq_of_perm permutation

/-- Common-apex restoration commutes with rebuilding the outer parallel node.
This uses only preservation of list length; atom values are still not
canonicalized recursively. -/
theorem substituteAt_collapseParallel
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl) :
    forall patterns : List Pattern,
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration patterns) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
        (patterns.map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth))
  | [] => by
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
        ReflectiveContextSupport.substituteAt]
  | first :: remaining => by
      cases remaining with
      | nil =>
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
      | cons second tail =>
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
            ReflectiveContextSupport.substituteAt]

/-- Restoring a complete keyed parallel normalization is the collision-free
canonical representative of the restored outer multiset. -/
theorem substituteAt_collapseParallel_normalizeParallelElementsBy_commonSemanticPatternKeyAt
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
            (cospan.commonSemanticPatternKeyAt source availableDepth)
            declaration patterns)) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
          ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
            declaration patterns).map
              (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
                cospan.commonSupport cospan.commonAssignment
                availableDepth))) := by
  rw [cospan.substituteAt_collapseParallel source availableDepth declaration]
  rw [cospan.map_normalizeParallelElementsBy_commonSemanticPatternKeyAt source]

/-- Full outer parallel reconstruction is invariant under any permutation of
restored contents.  This is the exact semantic terminal for a foreign-colour
parallel occurrence. -/
theorem substituteAt_collapseParallel_normalizeParallelElementsBy_commonSemanticPatternKeyAt_eq_of_perm
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl)
    {leftPatterns rightPatterns : List Pattern}
    (permutation : List.Perm
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration leftPatterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration rightPatterns).map
          (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment availableDepth))) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
            (cospan.commonSemanticPatternKeyAt source availableDepth)
            declaration leftPatterns)) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
            (cospan.commonSemanticPatternKeyAt source availableDepth)
            declaration rightPatterns)) := by
  rw [cospan.substituteAt_collapseParallel_normalizeParallelElementsBy_commonSemanticPatternKeyAt
      source,
    cospan.substituteAt_collapseParallel_normalizeParallelElementsBy_commonSemanticPatternKeyAt
      source]
  exact congrArg
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration)
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns_eq_of_perm permutation)

/-- Common-apex keyed canonicalization of a parallel frame depends only on
the multiset of its recursively normalized, restored outer contents.

The recursive element normalizer is applied before this theorem's premise is
formed.  The theorem itself then observes those elements only through common
restoration, so an opaque foreign-colour child is never canonicalized again
under the surrounding declaration. -/
theorem substituteAt_canonicalizeByAt_parallel_eq_of_perm
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (source : CIGSLT) (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl)
    {leftPatterns rightPatterns : List Pattern}
    (permutation : List.Perm
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth leftPatterns)).map
            (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
              cospan.commonSupport cospan.commonAssignment availableDepth))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth rightPatterns)).map
            (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
              cospan.commonSupport cospan.commonAssignment availableDepth))) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (.collection declaration.parallelCollection leftPatterns none)) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (.collection declaration.parallelCollection rightPatterns none)) := by
  simp only [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt,
    beq_self_eq_true, if_true]
  exact
    cospan.substituteAt_collapseParallel_normalizeParallelElementsBy_commonSemanticPatternKeyAt_eq_of_perm
      source availableDepth declaration permutation

end CostStaticAtomKeyCospan

namespace CostStaticAtomEnvironment

/-- Rename one endpoint atom into its slot in a common semantic quotient.
Names outside the finite endpoint inventory remain unchanged. -/
def sourceReificationName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (name : String) : String :=
  match environment.lookupAtom? name with
  | some slot => cospan.commonAtomName (leg slot)
  | none => name

/-- The endpoint-to-common name action preserves exactly the source typing
and reflective-support fibres recorded by the semantic key. -/
def sourceReificationRenaming
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key) :
    ReflectiveFVarRenaming environment.sourceAtomFreeContext
      cospan.commonSourceFreeContext environment.sourceAtomSupport
      cospan.commonSupport where
  name := environment.sourceReificationName cospan leg
  mapsLookup := by
    intro name type lookup
    cases selected : environment.lookupAtom? name with
    | none =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.sourceType) =
            some type at lookup
        simp [selected] at lookup
    | some slot =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.sourceType) =
            some type at lookup
        rw [selected] at lookup
        have sourceTypeEq : (environment.atomValue slot).key.sourceType =
            type := Option.some.inj lookup
        simp only [sourceReificationName, selected,
          cospan.commonSourceFreeContext_commonAtomName]
        rw [congrArg CostStaticAtomKey.sourceType (commutes slot), sourceTypeEq]
  mapsSupport := by
    intro name type lookup
    cases selected : environment.lookupAtom? name with
    | none =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.sourceType) =
            some type at lookup
        simp [selected] at lookup
    | some slot =>
        simp only [sourceReificationName, selected,
          cospan.commonSupport_commonAtomName]
        rw [congrArg CostStaticAtomKey.targetSupport (commutes slot)]
        simp [CostStaticAtomEnvironment.sourceAtomSupport, selected]

/-- The generic structural free-variable renamer computes exactly the direct
common-cospan reifier. -/
theorem renameFVars_sourceReificationName_eq_reifyWith
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length) :
    forall pattern,
      Pattern.renameFVars (environment.sourceReificationName cospan leg)
          pattern =
        cospan.reifyWith environment.lookupAtom? leg pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyWith]
  | hfvar name =>
      cases selected : environment.lookupAtom? name <;>
        simp [Pattern.renameFVars, sourceReificationName,
          CostStaticAtomKeyCospan.reifyWith, selected]
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyWith,
        Pattern.apply.injEq, true_and]
      exact List.map_congr_left inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyWith,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyWith,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyWith,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyWith,
        Pattern.collection.injEq, true_and, and_true]
      exact List.map_congr_left inductionHypothesis

/-- Common-cospan reification preserves source typing and arbitrary mapped
binder support.  This is the typed bridge needed before applying an authored
open canonical section at the common semantic apex. -/
theorem reifyWith_sourceReflectiveSupportSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType
      source.theory.presentation.presentation.language
      environment.sourceAtomFreeContext bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr -> TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.reflection.1
      environment.sourceAtomSupport available binderImage) :
    exists retyped : WellSorted.HasType
        source.theory.presentation.presentation.language
        cospan.commonSourceFreeContext bound
        (cospan.reifyWith environment.lookupAtom? leg pattern) type,
      retyped.ReflectiveSupportSafeAt source.reflection.1
        cospan.commonSupport available binderImage := by
  simpa only [sourceReificationRenaming,
    environment.renameFVars_sourceReificationName_eq_reifyWith
      cospan leg pattern] using
    safe.renameFVars
      (environment.sourceReificationRenaming cospan leg commutes)

/-- The same endpoint-to-common name action preserves generated target
typing.  This is distinct from `sourceReificationRenaming`: atom keys retain
both authored source types and generated target types, and the hereditary
frame being compared lives in the latter fibre. -/
def targetReificationRenaming
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key) :
    ReflectiveFVarRenaming environment.atomFreeContext
      cospan.commonTargetFreeContext environment.restorationSupport
      cospan.commonSupport where
  name := environment.sourceReificationName cospan leg
  mapsLookup := by
    intro name type lookup
    cases selected : environment.lookupAtom? name with
    | none =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.targetType) =
            some type at lookup
        simp [selected] at lookup
    | some slot =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.targetType) =
            some type at lookup
        rw [selected] at lookup
        have targetTypeEq : (environment.atomValue slot).key.targetType =
            type := Option.some.inj lookup
        simp only [sourceReificationName, selected,
          cospan.commonTargetFreeContext_commonAtomName]
        rw [congrArg CostStaticAtomKey.targetType (commutes slot),
          targetTypeEq]
  mapsSupport := by
    intro name type lookup
    cases selected : environment.lookupAtom? name with
    | none =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.targetType) =
            some type at lookup
        simp [selected] at lookup
    | some slot =>
        simp only [sourceReificationName, selected,
          cospan.commonSupport_commonAtomName]
        rw [congrArg CostStaticAtomKey.targetSupport (commutes slot)]
        simp [CostStaticAtomEnvironment.restorationSupport, selected]

/-- Common-cospan reification preserves generated target typing and its exact
reflective support.  This supplies typed common-namespace endpoints for the
recursive restoration-apex construction; raw syntax is never re-parsed. -/
theorem reifyWith_targetReflectiveSupportSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType source.costWholeLanguage
      environment.atomFreeContext bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile
      environment.restorationSupport available binderImage) :
    ∃ retyped : WellSorted.HasType source.costWholeLanguage
        cospan.commonTargetFreeContext bound
        (cospan.reifyWith environment.lookupAtom? leg pattern) type,
      retyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
        cospan.commonSupport available binderImage := by
  simpa only [targetReificationRenaming,
    environment.renameFVars_sourceReificationName_eq_reifyWith
      cospan leg pattern] using
    safe.renameFVars
      (environment.targetReificationRenaming cospan leg commutes)

/-- Move a complete source static term into the common semantic namespace.
Typing, constructor-fragment evidence, object admissibility, binder metadata,
reflective scope, and the selected Cost binder image all travel together. -/
noncomputable def reifySourceTermToCommon
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {sourceBound targetBound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      source.theory.presentation.presentation.language}
    (term : CostStaticRegionNode.CostStaticSourceTerm source color
      environment.sourceAtomFreeContext environment.sourceAtomSupport
      sourceBound targetBound sort) :
    CostStaticRegionNode.CostStaticSourceTerm source color
      cospan.commonSourceFreeContext cospan.commonSupport sourceBound
      targetBound sort := by
  classical
  let renamedEvidence :=
    environment.reifyWith_sourceReflectiveSupportSafeAt cospan leg commutes
      term.safe
  let retyped := Classical.choose renamedEvidence
  have retypedSafe := Classical.choose_spec renamedEvidence
  have patternEquality :
      Pattern.renameFVars (environment.sourceReificationName cospan leg)
          term.term.1 =
        cospan.reifyWith environment.lookupAtom? leg term.term.1 :=
    environment.renameFVars_sourceReificationName_eq_reifyWith
      cospan leg term.term.1
  have canonicalBinderMetadata :
      (cospan.reifyWith environment.lookupAtom? leg
          term.term.1).hasCanonicalBinderMetadata = true := by
    rw [← patternEquality,
      Pattern.hasCanonicalBinderMetadata_renameFVars]
    exact term.term.2.1.2.1
  have objectPattern : WellSorted.isObjectPattern
      (cospan.reifyWith environment.lookupAtom? leg term.term.1) = true := by
    rw [← patternEquality, WellSorted.isObjectPattern_renameFVars]
    exact term.term.2.1.2.2.1
  have reflectiveScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.reflection.1 sourceBound.length
      (cospan.reifyWith environment.lookupAtom? leg term.term.1) := by
    rw [← patternEquality]
    exact (WellSorted.reflectiveScopeSafeAt_renameFVars
      source.reflection.1
      (environment.sourceReificationName cospan leg) sourceBound.length
      term.term.1).mpr term.term.2.2
  have rawSupport : ConstructorsWithin
      (· ∈ source.continuationRetyping.wrappedLabels)
      (cospan.reifyWith environment.lookupAtom? leg term.term.1) := by
    rw [← patternEquality]
    exact term.supported.constructorsWithin.renameFVars
      (environment.sourceReificationName cospan leg)
  let supported := retyped.withConstructors rawSupport
    source.bareCollectionConstructorsWrapped
  exact
    { term := ⟨cospan.reifyWith environment.lookupAtom? leg term.term.1,
        ⟨⟨retyped, canonicalBinderMetadata, objectPattern,
          retyped.isWellScopedAt⟩, reflectiveScope⟩⟩
      supported := supported
      safe := retypedSafe }

@[simp]
theorem reifySourceTermToCommon_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {sourceBound targetBound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      source.theory.presentation.presentation.language}
    (term : CostStaticRegionNode.CostStaticSourceTerm source color
      environment.sourceAtomFreeContext environment.sourceAtomSupport
      sourceBound targetBound sort) :
    (environment.reifySourceTermToCommon cospan leg commutes term).term.1 =
      cospan.reifyWith environment.lookupAtom? leg term.term.1 := by
  rfl

/-- Move a complete generated target term into the common semantic namespace.
The returned subtype retains the exact reflective-support certificate used by
hereditary restoration.  In particular, this is transport of the existing
typed carrier through a finite-key cospan, not a second syntax-directed type
checker. -/
noncomputable def reifyTargetTermToCommon
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {bound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      environment.atomFreeContext bound sort)
    {available : List TypeExpr} {binderImage : TypeExpr -> TypeExpr}
    (safe : term.2.1.1.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile environment.restorationSupport
      available binderImage) :
    { commonTerm : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage
        cospan.commonTargetFreeContext bound sort //
      commonTerm.2.1.1.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile cospan.commonSupport available
        binderImage } := by
  classical
  let renamedEvidence :=
    environment.reifyWith_targetReflectiveSupportSafeAt cospan leg commutes safe
  let retyped := Classical.choose renamedEvidence
  have retypedSafe := Classical.choose_spec renamedEvidence
  have patternEquality :
      Pattern.renameFVars (environment.sourceReificationName cospan leg)
          term.1 =
        cospan.reifyWith environment.lookupAtom? leg term.1 :=
    environment.renameFVars_sourceReificationName_eq_reifyWith
      cospan leg term.1
  have canonicalBinderMetadata :
      (cospan.reifyWith environment.lookupAtom? leg
          term.1).hasCanonicalBinderMetadata = true := by
    rw [<- patternEquality,
      Pattern.hasCanonicalBinderMetadata_renameFVars]
    exact term.2.1.2.1
  have objectPattern : WellSorted.isObjectPattern
      (cospan.reifyWith environment.lookupAtom? leg term.1) = true := by
    rw [<- patternEquality, WellSorted.isObjectPattern_renameFVars]
    exact term.2.1.2.2.1
  have reflectiveScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile bound.length
      (cospan.reifyWith environment.lookupAtom? leg term.1) := by
    rw [<- patternEquality]
    exact (WellSorted.reflectiveScopeSafeAt_renameFVars
      source.costWholeReflectionProfile
      (environment.sourceReificationName cospan leg) bound.length term.1).mpr
        term.2.2
  exact
    ⟨⟨cospan.reifyWith environment.lookupAtom? leg term.1,
        ⟨⟨retyped, canonicalBinderMetadata, objectPattern,
          retyped.isWellScopedAt⟩, reflectiveScope⟩⟩,
      retypedSafe⟩

@[simp]
theorem reifyTargetTermToCommon_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {bound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      environment.atomFreeContext bound sort)
    {available : List TypeExpr} {binderImage : TypeExpr -> TypeExpr}
    (safe : term.2.1.1.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile environment.restorationSupport
      available binderImage) :
    (environment.reifyTargetTermToCommon cospan leg commutes term safe).1.1 =
      cospan.reifyWith environment.lookupAtom? leg term.1 := by
  rfl

/-- Common-cospan transport changes only semantic-atom names and therefore
preserves any constructor-fragment certificate carried by the target term. -/
theorem reifyTargetTermToCommon_constructorsWithin
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {bound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      environment.atomFreeContext bound sort)
    {available : List TypeExpr} {binderImage : TypeExpr -> TypeExpr}
    (safe : term.2.1.1.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile environment.restorationSupport
      available binderImage)
    {allowed : String -> Prop}
    (supported : ConstructorsWithin allowed term.1) :
    ConstructorsWithin allowed
      (environment.reifyTargetTermToCommon cospan leg commutes term safe).1.1 := by
  rw [environment.reifyTargetTermToCommon_pattern cospan leg commutes term safe,
    <- environment.renameFVars_sourceReificationName_eq_reifyWith cospan leg
      term.1]
  exact supported.renameFVars _

/-- A canonical frame is covered when every free name resolves to a slot in
its proof-relevant finite semantic-atom environment. -/
def Covers
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (pattern : Pattern) : Prop :=
  forall name, name ∈ pattern.freeFvarNames ->
    exists slot, environment.lookupAtom? name = some slot

/-- Atom coverage is invariant under every two-depth keyed reflective
canonicalizer. -/
theorem covers_canonicalizeByDepths_iff
    {Key : Type} [LinearOrder Key]
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (key : Nat -> Nat -> Pattern -> Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (pattern : Pattern) :
    environment.Covers
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
          key declaration availableDepth scopeDepth pattern) <->
      environment.Covers pattern := by
  constructor
  · intro covered name membership
    apply covered name
    exact (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
      key declaration name availableDepth scopeDepth pattern).mpr membership
  · intro covered name membership
    apply covered name
    exact (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
      key declaration name availableDepth scopeDepth pattern).mp membership

/-- Reifying positional parameter names into endpoint atoms and then into a
common semantic apex equals the direct positional-to-apex map, provided every
free occurrence is represented by the endpoint inventory. -/
theorem reifyWith_reify_eq_reifyWith
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length) :
    forall pattern,
      (forall name, name ∈ pattern.freeFvarNames ->
        exists slot, environment.slotOfName? name = some slot) ->
      cospan.reifyWith environment.lookupAtom? leg
          (environment.reify pattern) =
        cospan.reifyWith environment.slotOfName? leg pattern := by
  intro pattern covered
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp [CostStaticAtomEnvironment.reify,
        CostStaticAtomKeyCospan.reifyWith]
  | hfvar name =>
      obtain ⟨slot, selected⟩ :=
        covered name (by simp [Pattern.freeFvarNames])
      simp [CostStaticAtomEnvironment.reify,
        CostStaticAtomEnvironment.reifyName,
        CostStaticAtomKeyCospan.reifyWith, selected]
  | happly constructor arguments inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify,
        CostStaticAtomKeyCospan.reifyWith, List.map_map,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_flatMap]
      exact ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify,
        CostStaticAtomKeyCospan.reifyWith, Pattern.lambda.injEq, true_and]
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify,
        CostStaticAtomKeyCospan.reifyWith,
        Pattern.multiLambda.injEq, true_and]
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [CostStaticAtomEnvironment.reify,
        CostStaticAtomKeyCospan.reifyWith, Pattern.subst.injEq]
      constructor
      · apply bodyInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
      · apply replacementInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify,
        CostStaticAtomKeyCospan.reifyWith, List.map_map,
        Pattern.collection.injEq, true_and]
      constructor
      · apply List.map_congr_left
        intro element membership
        apply inductionHypothesis element membership
        intro name nameMembership
        apply covered name
        simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨element, membership, nameMembership⟩
      · trivial

/-- The atomized target frame followed by a common-cospan leg is exactly the
direct common reification of the selected mapped skeleton. -/
theorem reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length) :
    cospan.reifyWith environment.lookupAtom? leg
        (node.reifyTargetFrame environment) =
      cospan.reifyWith environment.slotOfName? leg
        node.mappedThickenedSkeleton.1 := by
  unfold CostStaticRegionNode.reifyTargetFrame
  apply environment.reifyWith_reify_eq_reifyWith cospan leg
  intro name membership
  have sourceMembership : name ∈ node.skeleton.1.freeFvarNames := by
    simpa using membership
  obtain ⟨occurrence, occurrenceName⟩ :=
    node.skeleton_fvar_covered name sourceMembership
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence occurrence)
  refine ⟨slot, ?_⟩
  simpa [occurrenceName] using selected

/-- Restoring a canonical semantic-atom name agrees exactly with restoring
the original positional occurrence that selected the same atom.  Occurrence
identity is retained in the hypothesis; only support and normalized value
are compared by this theorem. -/
theorem substituteAt_atomName_eq_substituteAt_occurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        environment.restorationSupport environment.restorationAssignment
        availableDepth (.fvar (environment.atomName slot)) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        table.restorationSupport (values.assignment table) availableDepth
        (.fvar occurrence.name) := by
  have supportEquality :=
    environment.atomValue_targetSupport_eq_of_slotOfName?_eq_some occurrence
      slot selected
  have valueEquality :=
    environment.atomValue_normal_eq_of_slotOfName?_eq_some occurrence slot
      selected
  simp only [ReflectiveContextSupport.substituteAt,
    environment.restorationSupport_atomName,
    environment.restorationAssignment_atomName]
  rw [supportEquality, valueEquality]

/-- Canonical common semantic quotient of two proof-relevant atom
environments.  The endpoint occurrence maps remain in the two environments;
this cospan compares only their complete typed evaluated keys. -/
def semanticKeyCospan
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
      rightInventory) :
    CostStaticAtomKeyCospan
      (fun slot => (left.atomValue slot).key)
      (fun slot => (right.atomValue slot).key) :=
  CostStaticAtomKeyCospan.ofFunctions
    (fun slot => (left.atomValue slot).key)
    (fun slot => (right.atomValue slot).key)

/-- Every common semantic slot retains a proof-relevant typed origin in at
least one endpoint environment. -/
theorem semanticKeyCospan_has_endpoint_origin
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
    (slot : Fin (left.semanticKeyCospan right).commonKeys.length) :
    (∃ leftSlot,
        (left.semanticKeyCospan right).commonKeys.get slot =
          (left.atomValue leftSlot).key) ∨
      ∃ rightSlot,
        (left.semanticKeyCospan right).commonKeys.get slot =
          (right.atomValue rightSlot).key := by
  exact CostStaticAtomKeyCospan.ofFunctions_has_endpoint_origin
    (fun leftSlot => (left.atomValue leftSlot).key)
    (fun rightSlot => (right.atomValue rightSlot).key) slot

/-- When both endpoint inventories belong to one selected colour, the
endpoint type-map certificates induce a uniform type map on their common
semantic quotient.  No representative is chosen: each common slot is
transported from whichever proof-relevant endpoint origin witnesses it. -/
theorem semanticKeyCospan_typeMap_of_sameColor
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
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (leftTypeMap : ∀ slot,
      mapTypeExpr (color.symbols source)
          (left.atomValue slot).key.sourceType =
        (left.atomValue slot).key.targetType)
    (rightTypeMap : ∀ slot,
      mapTypeExpr (color.symbols source)
          (right.atomValue slot).key.sourceType =
        (right.atomValue slot).key.targetType) :
    ∀ slot,
      mapTypeExpr (color.symbols source)
          ((left.semanticKeyCospan right).commonKeys.get slot).sourceType =
        ((left.semanticKeyCospan right).commonKeys.get slot).targetType := by
  intro slot
  rcases left.semanticKeyCospan_has_endpoint_origin right slot with
      ⟨leftSlot, keyEq⟩ | ⟨rightSlot, keyEq⟩
  · rw [keyEq]
    exact leftTypeMap leftSlot
  · rw [keyEq]
    exact rightTypeMap rightSlot

/-- The common semantic quotient restores through a genuine typed open
assignment.  Typing and object evidence for each quotient slot are inherited
from an endpoint origin; the proof-free common key merely transports those
proofs across its recorded equality. -/
def semanticKeyCospanSupportedOpenAssignment
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
      rightInventory) :
    WellSorted.SupportedOpenAssignment source.costWholeReflectionProfile source.costWholeLanguage
      (left.semanticKeyCospan right).commonTargetFreeContext targetFree
      (left.semanticKeyCospan right).commonSupport where
  assignment := (left.semanticKeyCospan right).commonAssignment
  typed := by
    intro name type lookup
    change ((left.semanticKeyCospan right).lookupCommon? name).map
      (fun slot =>
        ((left.semanticKeyCospan right).commonKeys.get slot).targetType) =
          some type at lookup
    cases selected : (left.semanticKeyCospan right).lookupCommon? name with
    | none => simp [selected] at lookup
    | some slot =>
        rw [selected] at lookup
        have targetTypeEq :
            ((left.semanticKeyCospan right).commonKeys.get slot).targetType =
              type := Option.some.inj lookup
        rcases left.semanticKeyCospan_has_endpoint_origin right slot with
            ⟨leftSlot, keyEq⟩ | ⟨rightSlot, keyEq⟩
        · have evidence := (left.atomValue leftSlot).normalTyped
          rw [← keyEq, targetTypeEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonSupport,
            CostStaticAtomKeyCospan.commonAssignment, selected, keyEq,
            targetTypeEq] using evidence
        · have evidence := (right.atomValue rightSlot).normalTyped
          rw [← keyEq, targetTypeEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonSupport,
            CostStaticAtomKeyCospan.commonAssignment, selected, keyEq,
            targetTypeEq] using evidence
  canonicalBinderMetadata := by
    intro name type lookup
    change ((left.semanticKeyCospan right).lookupCommon? name).map
      (fun slot =>
        ((left.semanticKeyCospan right).commonKeys.get slot).targetType) =
          some type at lookup
    cases selected : (left.semanticKeyCospan right).lookupCommon? name with
    | none => simp [selected] at lookup
    | some slot =>
        rcases left.semanticKeyCospan_has_endpoint_origin right slot with
            ⟨leftSlot, keyEq⟩ | ⟨rightSlot, keyEq⟩
        · have evidence :=
            (left.atomValue leftSlot).normalCanonicalBinderMetadata
          rw [← keyEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonAssignment, selected] using evidence
        · have evidence :=
            (right.atomValue rightSlot).normalCanonicalBinderMetadata
          rw [← keyEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonAssignment, selected] using evidence
  objectPattern := by
    intro name type lookup
    change ((left.semanticKeyCospan right).lookupCommon? name).map
      (fun slot =>
        ((left.semanticKeyCospan right).commonKeys.get slot).targetType) =
          some type at lookup
    cases selected : (left.semanticKeyCospan right).lookupCommon? name with
    | none => simp [selected] at lookup
    | some slot =>
        rcases left.semanticKeyCospan_has_endpoint_origin right slot with
            ⟨leftSlot, keyEq⟩ | ⟨rightSlot, keyEq⟩
        · have evidence := (left.atomValue leftSlot).normalObject
          rw [← keyEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonAssignment, selected] using evidence
        · have evidence := (right.atomValue rightSlot).normalObject
          rw [← keyEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonAssignment, selected] using evidence
  reflectiveScopeSafe := by
    intro name type lookup declaration membership
    change ((left.semanticKeyCospan right).lookupCommon? name).map
      (fun slot =>
        ((left.semanticKeyCospan right).commonKeys.get slot).targetType) =
          some type at lookup
    cases selected : (left.semanticKeyCospan right).lookupCommon? name with
    | none => simp [selected] at lookup
    | some slot =>
        rcases left.semanticKeyCospan_has_endpoint_origin right slot with
            ⟨leftSlot, keyEq⟩ | ⟨rightSlot, keyEq⟩
        · have evidence :=
            (left.atomValue leftSlot).normalReflectiveScopeSafe
              declaration membership
          rw [← keyEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonSupport,
            CostStaticAtomKeyCospan.commonAssignment, selected] using evidence
        · have evidence :=
            (right.atomValue rightSlot).normalReflectiveScopeSafe
              declaration membership
          rw [← keyEq] at evidence
          simpa [CostStaticAtomKeyCospan.commonSupport,
            CostStaticAtomKeyCospan.commonAssignment, selected] using evidence

/-- Rename one endpoint's authored atom namespace into a common semantic
namespace as a fully typed, support-indexed open assignment.

The assignment contains only rigid free variables.  Its typing is derived
from the cospan commuting law, while the endpoint support remains the source
support used by the authored reflective section.  Thus this construction is
a genuine change of finite namespace, not an evaluation or a hidden choice
of normalized representative. -/
def sourceReificationSupportedOpenAssignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key) :
    WellSorted.SupportedOpenAssignment
      source.reflection.1
      source.theory.presentation.presentation.language
      environment.sourceAtomFreeContext cospan.commonSourceFreeContext
  environment.sourceAtomSupport where
  assignment := fun name =>
    match environment.lookupAtom? name with
    | some slot => .fvar (cospan.commonAtomName (leg slot))
    | none => .fvar name
  typed := by
    intro name type lookup
    cases selected : environment.lookupAtom? name with
    | none =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.sourceType) =
            some type at lookup
        simp [selected] at lookup
    | some slot =>
        change (environment.lookupAtom? name).map
          (fun slot => (environment.atomValue slot).key.sourceType) =
            some type at lookup
        rw [selected] at lookup
        have sourceTypeEq : (environment.atomValue slot).key.sourceType =
            type := Option.some.inj lookup
        have commonLookup : cospan.commonSourceFreeContext
            (cospan.commonAtomName (leg slot)) = some type := by
          rw [cospan.commonSourceFreeContext_commonAtomName,
            congrArg CostStaticAtomKey.sourceType (commutes slot), sourceTypeEq]
        simpa [selected] using
          (WellSorted.HasType.fvar
            (language := source.theory.presentation.presentation.language)
            (bound := environment.sourceAtomSupport name) commonLookup)
  canonicalBinderMetadata := by
    intro name type lookup
    cases environment.lookupAtom? name <;> rfl
  objectPattern := by
    intro name type lookup
    cases environment.lookupAtom? name <;> rfl
  reflectiveScopeSafe := by
    intro name type lookup presentation membership
    cases environment.lookupAtom? name <;> rfl

/-- The supported source-namespace assignment computes exactly the direct
common-cospan reifier at every reflective binder depth.

All assignment images are free variables, so the support-indexed weakening
performed by `substituteAt` is inert.  The statement nevertheless retains
the support-aware API, making it suitable for rho's proved supported-
substitution theorem rather than an untyped renaming shortcut. -/
theorem sourceReificationSupportedOpenAssignment_substituteAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (availableDepth : Nat) (pattern : Pattern) :
    ReflectiveContextSupport.substituteAt
        source.reflection.1
        environment.sourceAtomSupport
        (environment.sourceReificationSupportedOpenAssignment cospan leg
          commutes).assignment availableDepth pattern =
      cospan.reifyWith environment.lookupAtom? leg pattern := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [ReflectiveContextSupport.substituteAt,
        CostStaticAtomKeyCospan.reifyWith]
  | hfvar name =>
      cases selected : environment.lookupAtom? name <;>
        simp [sourceReificationSupportedOpenAssignment,
          ReflectiveContextSupport.substituteAt,
          CostStaticAtomKeyCospan.reifyWith, selected,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        CostStaticAtomKeyCospan.reifyWith,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership _
  | hlambda binder body inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        CostStaticAtomKeyCospan.reifyWith, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis _
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        CostStaticAtomKeyCospan.reifyWith, Pattern.multiLambda.injEq,
        true_and]
      exact inductionHypothesis _
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [ReflectiveContextSupport.substituteAt,
        CostStaticAtomKeyCospan.reifyWith, Pattern.subst.injEq]
      exact ⟨bodyInduction _, replacementInduction _⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        CostStaticAtomKeyCospan.reifyWith,
        Pattern.collection.injEq, true_and, and_true]
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership _

/-- Cross-environment slots coalesce in the canonical joint exactly when
their complete typed semantic keys agree. -/
theorem semanticKeyCospan_crossExtensional
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
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount) :
    (left.semanticKeyCospan right).leftSlot leftSlot =
        (left.semanticKeyCospan right).rightSlot rightSlot <->
      (left.atomValue leftSlot).key = (right.atomValue rightSlot).key :=
  (left.semanticKeyCospan right).crossExtensional leftSlot rightSlot

/-- The same retagged authored source variable denotes the same complete
semantic atom across arbitrary proof-relevant boundary inventories in one
selected static fibre.  Boundary tables may differ; source-variable typing,
support, and literal value are all derived solely from the shared target
free context and colour. -/
theorem sourceVariable_key_eq
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
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (name : String)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (leftName : leftOccurrence.name = costRegionSourceVariableName name)
    (rightName : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (leftSelected : left.slotOfName? leftOccurrence.name = some leftSlot)
    (rightSelected : right.slotOfName? rightOccurrence.name = some rightSlot) :
    (left.atomValue leftSlot).key = (right.atomValue rightSlot).key := by
  have leftSourceType :=
    left.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected
  have rightSourceType :=
    right.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected
  have sourceContextEquality :
      leftTable.sourceFreeContext leftOccurrence.name =
        rightTable.sourceFreeContext rightOccurrence.name := by
    rw [leftName, rightName]
    simp
  have sourceTypeEquality :
      (left.atomValue leftSlot).key.sourceType =
        (right.atomValue rightSlot).key.sourceType :=
    Option.some.inj
      (leftSourceType.symm.trans
        (sourceContextEquality.trans rightSourceType))
  have leftTargetType :=
    left.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected
  have rightTargetType :=
    right.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected
  have targetContextEquality :
      leftTable.mappedFreeContext leftOccurrence.name =
        rightTable.mappedFreeContext rightOccurrence.name := by
    rw [leftName, rightName]
    simp [TypedCostRegionBoundaryTable.mappedFreeContext]
  have targetTypeEquality :
      (left.atomValue leftSlot).key.targetType =
        (right.atomValue rightSlot).key.targetType :=
    Option.some.inj
      (leftTargetType.symm.trans
        (targetContextEquality.trans rightTargetType))
  have leftSourceSupport :=
    left.atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected
  have rightSourceSupport :=
    right.atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected
  have sourceSupportEquality :
      (left.atomValue leftSlot).key.sourceSupport =
        (right.atomValue rightSlot).key.sourceSupport := by
    rw [leftSourceSupport, rightSourceSupport, leftName, rightName]
    simp
  have leftTargetSupport :=
    left.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected
  have rightTargetSupport :=
    right.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected
  have targetSupportEquality :
      (left.atomValue leftSlot).key.targetSupport =
        (right.atomValue rightSlot).key.targetSupport := by
    rw [leftTargetSupport, rightTargetSupport, leftName, rightName]
    simp
  have leftNormal :=
    left.atomValue_normal_eq_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected
  have rightNormal :=
    right.atomValue_normal_eq_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected
  have normalEquality :
      (left.atomValue leftSlot).key.normal =
        (right.atomValue rightSlot).key.normal := by
    rw [leftNormal, rightNormal, leftName, rightName]
    simp [TypedCostRegionBoundaryTable.Values.assignment]
  exact CostStaticAtomKey.ext_components sourceTypeEquality
    sourceSupportEquality targetTypeEquality targetSupportEquality
    normalEquality

/-- Reifying a canonical atom frame through one leg of a common semantic
quotient and restoring at the apex agrees exactly with restoration through
the endpoint atom environment.

Unlike `substituteAt_reifyWith_eq_substituteAt` below, this theorem is about
the internal semantic-atom namespace produced after selected-frame
canonicalization.  Its coverage premise is therefore stated using
`lookupAtom?`, not positional source/boundary occurrences. -/
theorem substituteAt_reifyAtomsWith_eq_restoreAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (availableDepth : Nat) (pattern : Pattern)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ slot, environment.lookupAtom? name = some slot) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (cospan.reifyWith environment.lookupAtom? leg pattern) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        environment.restorationSupport environment.restorationAssignment
        availableDepth pattern := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      obtain ⟨slot, selected⟩ :=
        covered name (by simp [Pattern.freeFvarNames])
      have commonSupport :
          cospan.commonSupport (cospan.commonAtomName (leg slot)) =
            (environment.atomValue slot).key.targetSupport := by
        rw [cospan.commonSupport_commonAtomName]
        exact congrArg CostStaticAtomKey.targetSupport (commutes slot)
      have commonValue :
          cospan.commonAssignment (cospan.commonAtomName (leg slot)) =
            (environment.atomValue slot).key.normal := by
        rw [cospan.commonAssignment_commonAtomName]
        exact congrArg CostStaticAtomKey.normal (commutes slot)
      simp [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, selected, commonSupport,
        commonValue, CostStaticAtomEnvironment.restorationSupport,
        CostStaticAtomEnvironment.restorationAssignment]
  | happly constructor arguments inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_flatMap]
      exact ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
      congr 1
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
      congr 1
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
      congr 1
      · apply bodyInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
      · apply replacementInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      apply inductionHypothesis element membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨element, membership, nameMembership⟩

/-- On an atom-covered frame, the endpoint semantic ordering key is exactly
the pullback of the common cospan key along its commuting leg. -/
theorem semanticPatternKeyAt_eq_commonSemanticPatternKeyAt_reifyWith
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (availableDepth : Nat) (pattern : Pattern)
    (covered : environment.Covers pattern) :
    CostStaticRegionNode.semanticPatternKeyAt environment availableDepth
        pattern =
      cospan.commonSemanticPatternKeyAt source availableDepth
        (cospan.reifyWith environment.lookupAtom? leg pattern) := by
  have restoration := substituteAt_reifyAtomsWith_eq_restoreAt environment
    cospan leg commutes availableDepth pattern covered
  exact congrArg Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
    restoration.symm

/-- Parallel normalization commutes with a semantic cospan on atom-covered
inputs.  Unlike the purely syntactic pullback theorem, this version uses the
production key that restores each finite atom before comparison. -/
theorem reifyWith_normalizeParallelElementsBy_semanticPatternKeyAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (availableDepth : Nat) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern)
    (covered : forall pattern, pattern ∈ patterns ->
      environment.Covers pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (CostStaticRegionNode.semanticPatternKeyAt environment availableDepth)
        declaration patterns).map
        (cospan.reifyWith environment.lookupAtom? leg) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (cospan.commonSemanticPatternKeyAt source availableDepth) declaration
        (patterns.map (cospan.reifyWith environment.lookupAtom? leg)) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    let contents := parallelContents declaration patterns
    have contentsCovered : forall pattern, pattern ∈ contents ->
        environment.Covers pattern := by
      intro pattern patternMembership name nameMembership
      have aggregateMembership : name ∈
          contents.flatMap Pattern.freeFvarNames := by
        rw [List.mem_flatMap]
        exact ⟨pattern, patternMembership, nameMembership⟩
      have sourceMembership : name ∈
          patterns.flatMap Pattern.freeFvarNames :=
        (mem_flatMap_freeFvarNames_parallelContents_iff declaration name
          patterns).mp aggregateMembership
      rw [List.mem_flatMap] at sourceMembership
      obtain ⟨sourcePattern, sourcePatternMembership, sourceNameMembership⟩ :=
        sourceMembership
      exact covered sourcePattern sourcePatternMembership name
        sourceNameMembership
    have keyEquality :
        Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
            (CostStaticRegionNode.semanticPatternKeyAt environment
              availableDepth) contents =
          Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
            (fun pattern => cospan.commonSemanticPatternKeyAt source
              availableDepth
              (cospan.reifyWith environment.lookupAtom? leg pattern))
            contents := by
      apply CostStaticAtomKeyCospan.sortPatternsBy_eq_of_keys_eq_on
      intro pattern patternMembership
      exact semanticPatternKeyAt_eq_commonSemanticPatternKeyAt_reifyWith
        environment cospan leg commutes availableDepth pattern
          (contentsCovered pattern patternMembership)
    unfold normalizeParallelElementsBy
    change (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (CostStaticRegionNode.semanticPatternKeyAt environment availableDepth)
        contents).map (cospan.reifyWith environment.lookupAtom? leg) = _
    rw [keyEquality]
    rw [CostHereditaryCanonical.map_sortPatternsBy]
    exact congrArg
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (cospan.commonSemanticPatternKeyAt source availableDepth))
      (cospan.reifyWith_parallelContents environment.lookupAtom? leg
        declaration patterns)

/-- Production semantic-key canonicalization is natural through a common
semantic cospan on the exact atom-covered carrier.  The quote-visible depth
is preserved, parallel sorting is compared through restored semantic values,
and no ordering fact is recomputed at either endpoint. -/
theorem reifyWith_canonicalizeByDepths_semanticPatternKeyAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (declaration : ReflectivePresentationDecl) :
    forall availableDepth scopeDepth pattern,
      environment.Covers pattern ->
      cospan.reifyWith environment.lookupAtom? leg
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
            (fun availableDepth _ pattern =>
              CostStaticRegionNode.semanticPatternKeyAt environment
                availableDepth pattern)
            declaration availableDepth scopeDepth pattern) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
          (fun availableDepth _ pattern =>
            cospan.commonSemanticPatternKeyAt source availableDepth pattern)
          declaration availableDepth scopeDepth
          (cospan.reifyWith environment.lookupAtom? leg pattern) := by
  open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
    intro availableDepth scopeDepth pattern covered
    induction pattern using Pattern.inductionOn generalizing availableDepth
        scopeDepth with
    | hbvar index => simp [canonicalizeByDepths, CostStaticAtomKeyCospan.reifyWith]
    | hfvar name =>
        cases selected : environment.lookupAtom? name <;>
          simp [canonicalizeByDepths, CostStaticAtomKeyCospan.reifyWith,
            selected]
    | happly constructor arguments inductionHypothesis =>
        let childAvailableDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        have argumentCovered : forall argument, argument ∈ arguments ->
            environment.Covers argument := by
          intro argument argumentMembership name nameMembership
          apply covered name
          simp only [Pattern.freeFvarNames, List.mem_flatMap]
          exact ⟨argument, argumentMembership, nameMembership⟩
        have listFactor :
            (canonicalizeListByDepths
                (fun availableDepth _ pattern =>
                  CostStaticRegionNode.semanticPatternKeyAt environment
                    availableDepth pattern)
                declaration childAvailableDepth scopeDepth arguments).map
                (cospan.reifyWith environment.lookupAtom? leg) =
              canonicalizeListByDepths
                (fun availableDepth _ pattern =>
                  cospan.commonSemanticPatternKeyAt source availableDepth
                    pattern)
                declaration childAvailableDepth scopeDepth
                (arguments.map
                  (cospan.reifyWith environment.lookupAtom? leg)) := by
          rw [canonicalizeListByDepths_eq_map,
            canonicalizeListByDepths_eq_map]
          simp only [List.map_map]
          apply List.map_congr_left
          intro argument membership
          exact inductionHypothesis argument membership childAvailableDepth
            scopeDepth (argumentCovered argument membership)
        simp only [canonicalizeByDepths, CostStaticAtomKeyCospan.reifyWith]
        change cospan.reifyWith environment.lookupAtom? leg
            (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration constructor
              (canonicalizeListByDepths
                (fun availableDepth _ pattern =>
                  CostStaticRegionNode.semanticPatternKeyAt environment
                    availableDepth pattern)
                declaration childAvailableDepth scopeDepth arguments)) = _
        rw [cospan.reifyWith_finishNormalizeReflectiveApply, listFactor]
    | hlambda binder body inductionHypothesis =>
        have bodyCovered : environment.Covers body := by
          intro name nameMembership
          apply covered name
          simpa [Pattern.freeFvarNames] using nameMembership
        simp only [canonicalizeByDepths, CostStaticAtomKeyCospan.reifyWith,
          Pattern.lambda.injEq, true_and]
        exact inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
          bodyCovered
    | hmultiLambda arity binders body inductionHypothesis =>
        have bodyCovered : environment.Covers body := by
          intro name nameMembership
          apply covered name
          simpa [Pattern.freeFvarNames] using nameMembership
        simp only [canonicalizeByDepths, CostStaticAtomKeyCospan.reifyWith,
          Pattern.multiLambda.injEq, true_and]
        exact inductionHypothesis (availableDepth + arity)
          (scopeDepth + arity) bodyCovered
    | hsubst body replacement bodyInduction replacementInduction =>
        have bodyCovered : environment.Covers body := by
          intro name nameMembership
          apply covered name
          simp [Pattern.freeFvarNames, nameMembership]
        have replacementCovered : environment.Covers replacement := by
          intro name nameMembership
          apply covered name
          simp [Pattern.freeFvarNames, nameMembership]
        simp only [canonicalizeByDepths, CostStaticAtomKeyCospan.reifyWith,
          Pattern.subst.injEq]
        exact ⟨bodyInduction (availableDepth + 1) (scopeDepth + 1)
            bodyCovered,
          replacementInduction availableDepth scopeDepth replacementCovered⟩
    | hcollection collectionType elements rest inductionHypothesis =>
        have elementCovered : forall element, element ∈ elements ->
            environment.Covers element := by
          intro element elementMembership name nameMembership
          apply covered name
          simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
          exact Or.inl ⟨element, elementMembership, nameMembership⟩
        let endpointKey : Nat -> Nat -> Pattern -> Nat :=
          fun availableDepth _ pattern =>
            CostStaticRegionNode.semanticPatternKeyAt environment
              availableDepth pattern
        let commonKey : Nat -> Nat -> Pattern -> Nat :=
          fun availableDepth _ pattern =>
            cospan.commonSemanticPatternKeyAt source availableDepth pattern
        have listFactor :
            (canonicalizeListByDepths endpointKey declaration availableDepth
                scopeDepth elements).map
                (cospan.reifyWith environment.lookupAtom? leg) =
              canonicalizeListByDepths commonKey declaration availableDepth
                scopeDepth
                (elements.map
                  (cospan.reifyWith environment.lookupAtom? leg)) := by
          rw [canonicalizeListByDepths_eq_map,
            canonicalizeListByDepths_eq_map]
          simp only [List.map_map]
          apply List.map_congr_left
          intro element membership
          exact inductionHypothesis element membership availableDepth scopeDepth
            (elementCovered element membership)
        cases rest with
        | some restName =>
            simp only [canonicalizeByDepths,
              CostStaticAtomKeyCospan.reifyWith, Pattern.collection.injEq,
              true_and]
            exact ⟨listFactor, trivial⟩
        | none =>
            by_cases isParallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              have normalizedCovered : forall normalized,
                  normalized ∈ canonicalizeListByDepths endpointKey declaration
                    availableDepth scopeDepth elements ->
                    environment.Covers normalized := by
                intro normalized normalizedMembership
                rw [canonicalizeListByDepths_eq_map] at normalizedMembership
                obtain ⟨element, elementMembership, normalizedEquality⟩ :=
                  List.mem_map.mp normalizedMembership
                rw [← normalizedEquality]
                exact (environment.covers_canonicalizeByDepths_iff endpointKey
                  declaration availableDepth scopeDepth element).mpr
                    (elementCovered element elementMembership)
              simp only [canonicalizeByDepths,
                CostStaticAtomKeyCospan.reifyWith, beq_self_eq_true, if_true]
              rw [cospan.reifyWith_collapseParallel]
              rw [environment.reifyWith_normalizeParallelElementsBy_semanticPatternKeyAt
                cospan leg commutes availableDepth declaration
                (canonicalizeListByDepths endpointKey declaration
                  availableDepth scopeDepth elements) normalizedCovered]
              exact congrArg (fun normalizedElements =>
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                  declaration
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
                    (cospan.commonSemanticPatternKeyAt source availableDepth)
                    declaration normalizedElements))
                listFactor
            · have notParallel :
                  (collectionType == declaration.parallelCollection) = false :=
                beq_eq_false_iff_ne.mpr isParallel
              simpa [canonicalizeByDepths,
                CostStaticAtomKeyCospan.reifyWith, notParallel, isParallel]
                using congrArg
                  (fun normalizedElements =>
                    Pattern.collection collectionType normalizedElements none)
                  listFactor

/-- One-depth production canonicalization is the direct specialization of
the two-depth semantic-cospan naturality law. -/
theorem reifyWith_canonicalizeByAt_semanticPatternKeyAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth : Nat) (pattern : Pattern)
    (covered : environment.Covers pattern) :
    cospan.reifyWith environment.lookupAtom? leg
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt environment)
          declaration availableDepth pattern) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt source) declaration availableDepth
        (cospan.reifyWith environment.lookupAtom? leg pattern) := by
  simpa only [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_ignoreScope]
    using environment.reifyWith_canonicalizeByDepths_semanticPatternKeyAt
      cospan leg commutes declaration availableDepth 0 pattern covered

/-- If two covered endpoint frames already agree in the common semantic
namespace, their production semantic-key canonical representatives agree
there as well.  This is the reusable canonical-frame square: endpoint sort
orders are never compared directly. -/
theorem commonCanonicalFrames_eq_of_commonFrames_eq
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
    (cospan : CostStaticAtomKeyCospan
      (fun slot => (left.atomValue slot).key)
      (fun slot => (right.atomValue slot).key))
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (leftFrame rightFrame : Pattern)
    (leftCovered : left.Covers leftFrame)
    (rightCovered : right.Covers rightFrame)
    (commonFramesEq :
      cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame =
        cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame) :
    cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt left) declaration
          availableDepth leftFrame) =
      cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt right) declaration
          availableDepth rightFrame) := by
  calc
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame) :=
      left.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
        cospan.leftSlot cospan.leftCommutes declaration availableDepth
        leftFrame leftCovered
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame) :=
      congrArg
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth)
        commonFramesEq
    _ = _ :=
      (right.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
        cospan.rightSlot cospan.rightCommutes declaration availableDepth
        rightFrame rightCovered).symm

/-- If two covered endpoint frames have the same canonical representative in
the common semantic namespace, then their endpoint semantic-key canonical
representatives agree after reification through the cospan legs.

Unlike `commonCanonicalFrames_eq_of_commonFrames_eq`, this theorem permits an
authored generator to be absorbed by the canonicalizer at the common apex.
The premise is stated entirely in that apex; endpoint occurrence orderings
remain observationally irrelevant. -/
theorem commonCanonicalFrames_eq_of_commonCanonicalFrames_eq
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
    (cospan : CostStaticAtomKeyCospan
      (fun slot => (left.atomValue slot).key)
      (fun slot => (right.atomValue slot).key))
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (leftFrame rightFrame : Pattern)
    (leftCovered : left.Covers leftFrame)
    (rightCovered : right.Covers rightFrame)
    (commonCanonicalFramesEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame)) :
    cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt left) declaration
          availableDepth leftFrame) =
      cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt right) declaration
          availableDepth rightFrame) := by
  calc
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame) :=
      left.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
        cospan.leftSlot cospan.leftCommutes declaration availableDepth
        leftFrame leftCovered
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth
          (cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame) :=
      commonCanonicalFramesEq
    _ = _ :=
      (right.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
        cospan.rightSlot cospan.rightCommutes declaration availableDepth
        rightFrame rightCovered).symm

/-- Two covered endpoint frames have the same restored canonical result when
their common-apex presentations are parallel frames whose recursively
normalized outer contents agree up to permutation after restoration.

This is the foreign-colour terminal law.  Endpoint canonicalization remains
natural through the semantic cospan, while the final comparison forgets only
outer parallel order.  In particular, normalized boundary atoms stay opaque
throughout the selected frame. -/
theorem commonRestoredCanonicalFrames_eq_of_parallelFrames_of_perm
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
    (cospan : CostStaticAtomKeyCospan
      (fun slot => (left.atomValue slot).key)
      (fun slot => (right.atomValue slot).key))
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (leftFrame rightFrame : Pattern)
    (leftCovered : left.Covers leftFrame)
    (rightCovered : right.Covers rightFrame)
    {leftPatterns rightPatterns : List Pattern}
    (leftParallel :
      cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame =
        .collection declaration.parallelCollection leftPatterns none)
    (rightParallel :
      cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame =
        .collection declaration.parallelCollection rightPatterns none)
    (permutation : List.Perm
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth leftPatterns)).map
            (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
              cospan.commonSupport cospan.commonAssignment availableDepth))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source) declaration
          availableDepth rightPatterns)).map
            (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
              cospan.commonSupport cospan.commonAssignment availableDepth))) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
            (CostStaticRegionNode.semanticPatternKeyAt left) declaration
            availableDepth leftFrame)) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
            (CostStaticRegionNode.semanticPatternKeyAt right) declaration
            availableDepth rightFrame)) := by
  rw [left.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.leftSlot cospan.leftCommutes declaration availableDepth
      leftFrame leftCovered,
    right.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.rightSlot cospan.rightCommutes declaration availableDepth
      rightFrame rightCovered]
  rw [leftParallel, rightParallel]
  exact cospan.substituteAt_canonicalizeByAt_parallel_eq_of_perm source
    availableDepth declaration permutation

/-- Reifying any occurrence-covered endpoint frame through a commuting leg
of a common semantic cospan and restoring at the apex is exactly the original
finite supported substitution at that endpoint.

The theorem is structural and quote-aware.  The cospan leg may identify many
endpoint occurrences with one semantic slot, but `commutes` ensures that the
complete target support and normalized value are unchanged. -/
theorem substituteAt_reifyWith_eq_substituteAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (availableDepth : Nat) (pattern : Pattern)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence root,
        occurrence.name = name) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (cospan.reifyWith environment.slotOfName? leg pattern) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        table.restorationSupport (values.assignment table) availableDepth
        pattern := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      obtain ⟨occurrence, occurrenceName⟩ :=
        covered name (by simp [Pattern.freeFvarNames])
      obtain ⟨slot, selectedOccurrence⟩ := Option.isSome_iff_exists.mp
        (environment.slotOfName?_isSome_of_occurrence occurrence)
      have selected : environment.slotOfName? name = some slot := by
        simpa [occurrenceName] using selectedOccurrence
      have endpointSupport :
          (environment.atomValue slot).key.targetSupport =
            table.restorationSupport name := by
        simpa [occurrenceName] using
          environment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
            occurrence slot selectedOccurrence
      have endpointValue : (environment.atomValue slot).key.normal =
          values.assignment table name := by
        simpa [occurrenceName] using
          environment.atomValue_normal_eq_of_slotOfName?_eq_some
            occurrence slot selectedOccurrence
      have commonSupport :
          cospan.commonSupport (cospan.commonAtomName (leg slot)) =
            (environment.atomValue slot).key.targetSupport := by
        rw [cospan.commonSupport_commonAtomName]
        exact congrArg CostStaticAtomKey.targetSupport (commutes slot)
      have commonValue :
          cospan.commonAssignment (cospan.commonAtomName (leg slot)) =
            (environment.atomValue slot).key.normal := by
        rw [cospan.commonAssignment_commonAtomName]
        exact congrArg CostStaticAtomKey.normal (commutes slot)
      simp [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, selected, commonSupport,
        commonValue, endpointSupport, endpointValue]
  | happly constructor arguments inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_flatMap]
      exact ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
      congr 1
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
      congr 1
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt]
      congr 1
      · apply bodyInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
      · apply replacementInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      apply inductionHypothesis element membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨element, membership, nameMembership⟩

/-- Left-leg specialization of the common restoration factorization. -/
theorem substituteAt_reifyLeft_eq_substituteAt
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
    (availableDepth : Nat) (pattern : Pattern)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence leftRoot,
        occurrence.name = name) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        (left.semanticKeyCospan right).commonSupport
        (left.semanticKeyCospan right).commonAssignment availableDepth
        ((left.semanticKeyCospan right).reifyLeft left.slotOfName? pattern) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        leftTable.restorationSupport (leftValues.assignment leftTable)
        availableDepth pattern := by
  exact substituteAt_reifyWith_eq_substituteAt left
    (left.semanticKeyCospan right) (left.semanticKeyCospan right).leftSlot
    (left.semanticKeyCospan right).leftCommutes availableDepth pattern covered

/-- Right-leg specialization of the common restoration factorization. -/
theorem substituteAt_reifyRight_eq_substituteAt
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
    (availableDepth : Nat) (pattern : Pattern)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence rightRoot,
        occurrence.name = name) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        (left.semanticKeyCospan right).commonSupport
        (left.semanticKeyCospan right).commonAssignment availableDepth
        ((left.semanticKeyCospan right).reifyRight right.slotOfName? pattern) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        rightTable.restorationSupport (rightValues.assignment rightTable)
        availableDepth pattern := by
  exact substituteAt_reifyWith_eq_substituteAt right
    (left.semanticKeyCospan right) (left.semanticKeyCospan right).rightSlot
    (left.semanticKeyCospan right).rightCommutes availableDepth pattern covered

end CostStaticAtomEnvironment

/-! ## Root-changing frame alignment -/

/-- Proof-relevant alignment of two evaluated static frames through one
finite semantic-atom apex.

The endpoint environments retain their positional source/boundary
occurrences.  The cospan may coalesce equal semantic keys, while the two
coverage fields certify that every free parameter of each compared frame is
still represented by an endpoint occurrence.  `reifiedFrames_eq` is stated
before restoration, so this certificate does not merely store the desired
equality of final compact patterns. -/
structure CostStaticAtomFrameAlignment
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
    (leftFrame rightFrame : Pattern) where
  cospan : CostStaticAtomKeyCospan
    (fun slot => (left.atomValue slot).key)
    (fun slot => (right.atomValue slot).key)
  leftCovered : ∀ name, name ∈ leftFrame.freeFvarNames →
    ∃ occurrence : CostStaticFVarOccurrence leftRoot,
      occurrence.name = name
  rightCovered : ∀ name, name ∈ rightFrame.freeFvarNames →
    ∃ occurrence : CostStaticFVarOccurrence rightRoot,
      occurrence.name = name
  reifiedFrames_eq :
    cospan.reifyWith left.slotOfName? cospan.leftSlot leftFrame =
      cospan.reifyWith right.slotOfName? cospan.rightSlot rightFrame

namespace CostStaticAtomFrameAlignment

/-- Reverse a positional semantic-atom frame alignment without forgetting
either endpoint inventory or its common semantic quotient. -/
def symm
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    (alignment : CostStaticAtomFrameAlignment left right leftFrame rightFrame) :
    CostStaticAtomFrameAlignment right left rightFrame leftFrame where
  cospan := alignment.cospan.symm
  leftCovered := alignment.rightCovered
  rightCovered := alignment.leftCovered
  reifiedFrames_eq := by
    simpa only [CostStaticAtomKeyCospan.symm_reifyWith,
      CostStaticAtomKeyCospan.symm_leftSlot,
      CostStaticAtomKeyCospan.symm_rightSlot] using
      alignment.reifiedFrames_eq.symm

/-- Align two single-occurrence frames when their retained positional atoms
have the same complete typed semantic key. -/
def singleFvar
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
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (leftSelected : left.slotOfName? leftOccurrence.name = some leftSlot)
    (rightSelected : right.slotOfName? rightOccurrence.name = some rightSlot)
    (keyEquality : (left.atomValue leftSlot).key =
      (right.atomValue rightSlot).key) :
    CostStaticAtomFrameAlignment left right
      (.fvar leftOccurrence.name) (.fvar rightOccurrence.name) where
  cospan := left.semanticKeyCospan right
  leftCovered := by
    intro name membership
    have nameEquality : name = leftOccurrence.name := by
      simpa [Pattern.freeFvarNames] using membership
    exact ⟨leftOccurrence, nameEquality.symm⟩
  rightCovered := by
    intro name membership
    have nameEquality : name = rightOccurrence.name := by
      simpa [Pattern.freeFvarNames] using membership
    exact ⟨rightOccurrence, nameEquality.symm⟩
  reifiedFrames_eq := by
    simp only [CostStaticAtomKeyCospan.reifyWith, leftSelected,
      rightSelected]
    have slotEquality :
        (left.semanticKeyCospan right).leftSlot leftSlot =
          (left.semanticKeyCospan right).rightSlot rightSlot :=
      (CostStaticAtomEnvironment.semanticKeyCospan_crossExtensional left right
        leftSlot rightSlot).mpr keyEquality
    exact congrArg Pattern.fvar
      (congrArg (left.semanticKeyCospan right).commonAtomName
        slotEquality)

/-- A frame equality in the common semantic namespace descends to exact
equality of the two endpoint substitutions after restoring the common apex.

This is the generic root-crossing square.  It permits different endpoint
colours, boundary inventories, occurrence multiplicities, and raw parameter
spellings; equality is obtained only after both sides commute through the
same complete typed semantic keys. -/
theorem restoredFrames_eq
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    (alignment : CostStaticAtomFrameAlignment left right leftFrame rightFrame)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        leftTable.restorationSupport (leftValues.assignment leftTable)
        availableDepth leftFrame =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        rightTable.restorationSupport (rightValues.assignment rightTable)
        availableDepth rightFrame := by
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyWith_eq_substituteAt left
      alignment.cospan alignment.cospan.leftSlot
      alignment.cospan.leftCommutes availableDepth leftFrame
      alignment.leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyWith_eq_substituteAt right
      alignment.cospan alignment.cospan.rightSlot
      alignment.cospan.rightCommutes availableDepth rightFrame
      alignment.rightCovered
  calc
    _ = ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          alignment.cospan.commonSupport alignment.cospan.commonAssignment
          availableDepth
          (alignment.cospan.reifyWith left.slotOfName?
            alignment.cospan.leftSlot leftFrame) := leftFactor.symm
    _ = ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          alignment.cospan.commonSupport alignment.cospan.commonAssignment
          availableDepth
          (alignment.cospan.reifyWith right.slotOfName?
            alignment.cospan.rightSlot rightFrame) := by
      exact congrArg
        (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          alignment.cospan.commonSupport alignment.cospan.commonAssignment
          availableDepth)
        alignment.reifiedFrames_eq
    _ = _ := rightFactor

end CostStaticAtomFrameAlignment

/-- A local evaluator factors two possibly root-changing results through one
semantic-atom frame alignment.

The factorization fields relate each evaluator result to its own endpoint
substitution.  Exact equality of the two results is therefore derived from
the common semantic apex rather than stored as a field. -/
structure CostStaticAtomEvaluationBridge
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    (alignment : CostStaticAtomFrameAlignment left right leftFrame rightFrame)
    (availableDepth : Nat) (leftResult rightResult : Pattern) where
  leftFactors : leftResult =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      leftTable.restorationSupport (leftValues.assignment leftTable)
      availableDepth leftFrame
  rightFactors : rightResult =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      rightTable.restorationSupport (rightValues.assignment rightTable)
      availableDepth rightFrame

namespace CostStaticAtomEvaluationBridge

/-- Reverse an evaluation bridge by reversing its proof-relevant frame
alignment and exchanging the two endpoint factorizations. -/
def symm
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    {alignment : CostStaticAtomFrameAlignment left right leftFrame rightFrame}
    {availableDepth : Nat} {leftResult rightResult : Pattern}
    (bridge : CostStaticAtomEvaluationBridge alignment availableDepth
      leftResult rightResult) :
    CostStaticAtomEvaluationBridge alignment.symm availableDepth rightResult
      leftResult where
  leftFactors := bridge.rightFactors
  rightFactors := bridge.leftFactors

/-- Exact local evaluator agreement derived from the proof-relevant common
semantic-atom square. -/
theorem results_eq
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    {alignment : CostStaticAtomFrameAlignment left right leftFrame rightFrame}
    {availableDepth : Nat} {leftResult rightResult : Pattern}
    (bridge : CostStaticAtomEvaluationBridge alignment availableDepth
      leftResult rightResult) :
    leftResult = rightResult :=
  bridge.leftFactors.trans
    ((alignment.restoredFrames_eq availableDepth).trans
      bridge.rightFactors.symm)

end CostStaticAtomEvaluationBridge

/-- Existential package for one finite semantic-atom evaluation bridge.

The package hides only dependent indices.  It retains both endpoint colours,
finite boundary tables and values, positional inventories, environments,
pre-restoration frames, the common cospan alignment, and the restoration
depth.  Consequently it is suitable as a root-changing constructor of a
larger tree alignment without reducing the certificate to its result
equality. -/
structure PackedCostStaticAtomEvaluationBridge
    (source : CIGSLT) (leftResult rightResult : Pattern) where
  leftColor : CostStaticColor
  rightColor : CostStaticColor
  targetFree : WellSorted.FreeTypeContext
  leftOccurrences : List CostRegionOccurrence
  rightOccurrences : List CostRegionOccurrence
  leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
    leftOccurrences
  rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
    rightOccurrences
  leftValues : TypedCostRegionBoundaryTable.Values source leftColor targetFree
    leftTable
  rightValues : TypedCostRegionBoundaryTable.Values source rightColor
    targetFree rightTable
  leftRoot : Pattern
  rightRoot : Pattern
  leftInventory : CostStaticParameterInventory source leftColor targetFree
    leftTable leftValues leftRoot
  rightInventory : CostStaticParameterInventory source rightColor targetFree
    rightTable rightValues rightRoot
  leftEnvironment : CostStaticAtomEnvironment source leftColor targetFree
    leftInventory
  rightEnvironment : CostStaticAtomEnvironment source rightColor targetFree
    rightInventory
  leftFrame : Pattern
  rightFrame : Pattern
  alignment : CostStaticAtomFrameAlignment leftEnvironment rightEnvironment
    leftFrame rightFrame
  availableDepth : Nat
  bridge : CostStaticAtomEvaluationBridge alignment availableDepth leftResult
    rightResult

namespace PackedCostStaticAtomEvaluationBridge

/-- Reverse a packed semantic-atom evaluation bridge without erasing any
endpoint inventory, atom environment, or cospan evidence. -/
def symm
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (packed : PackedCostStaticAtomEvaluationBridge source leftResult
      rightResult) :
    PackedCostStaticAtomEvaluationBridge source rightResult leftResult where
  leftColor := packed.rightColor
  rightColor := packed.leftColor
  targetFree := packed.targetFree
  leftOccurrences := packed.rightOccurrences
  rightOccurrences := packed.leftOccurrences
  leftTable := packed.rightTable
  rightTable := packed.leftTable
  leftValues := packed.rightValues
  rightValues := packed.leftValues
  leftRoot := packed.rightRoot
  rightRoot := packed.leftRoot
  leftInventory := packed.rightInventory
  rightInventory := packed.leftInventory
  leftEnvironment := packed.rightEnvironment
  rightEnvironment := packed.leftEnvironment
  leftFrame := packed.rightFrame
  rightFrame := packed.leftFrame
  alignment := packed.alignment.symm
  availableDepth := packed.availableDepth
  bridge := packed.bridge.symm

/-- Package an already-constructed semantic-atom bridge while inferring all
of its dependent endpoint data. -/
def ofBridge
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
    {leftEnvironment : CostStaticAtomEnvironment source leftColor targetFree
      leftInventory}
    {rightEnvironment : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame leftResult rightResult : Pattern}
    {alignment : CostStaticAtomFrameAlignment leftEnvironment rightEnvironment
      leftFrame rightFrame}
    {availableDepth : Nat}
    (bridge : CostStaticAtomEvaluationBridge alignment availableDepth
      leftResult rightResult) :
    PackedCostStaticAtomEvaluationBridge source leftResult rightResult where
  leftColor := leftColor
  rightColor := rightColor
  targetFree := targetFree
  leftOccurrences := leftOccurrences
  rightOccurrences := rightOccurrences
  leftTable := leftTable
  rightTable := rightTable
  leftValues := leftValues
  rightValues := rightValues
  leftRoot := leftRoot
  rightRoot := rightRoot
  leftInventory := leftInventory
  rightInventory := rightInventory
  leftEnvironment := leftEnvironment
  rightEnvironment := rightEnvironment
  leftFrame := leftFrame
  rightFrame := rightFrame
  alignment := alignment
  availableDepth := availableDepth
  bridge := bridge

/-- Exact evaluator equality remains a derived theorem after existential
packaging. -/
theorem results_eq
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (packed : PackedCostStaticAtomEvaluationBridge source leftResult
      rightResult) :
    leftResult = rightResult :=
  packed.bridge.results_eq

end PackedCostStaticAtomEvaluationBridge

/-! ## Canonical semantic-atom frame alignment -/

/-- Alignment of two frames whose free names are already the internal names
of their endpoint semantic-atom environments.

`CostStaticAtomFrameAlignment` above compares positional source/boundary
names before atom restoration.  This sibling relation is deliberately
separate: it compares the canonical frames produced after atomization, where
`lookupAtom?` is the resolver and each endpoint environment is the restoring
authority. -/
structure CostStaticCanonicalAtomFrameAlignment
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
    (leftFrame rightFrame : Pattern) where
  cospan : CostStaticAtomKeyCospan
    (fun slot => (left.atomValue slot).key)
    (fun slot => (right.atomValue slot).key)
  leftCovered : ∀ name, name ∈ leftFrame.freeFvarNames →
    ∃ slot, left.lookupAtom? name = some slot
  rightCovered : ∀ name, name ∈ rightFrame.freeFvarNames →
    ∃ slot, right.lookupAtom? name = some slot
  reifiedFrames_eq :
    cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame =
      cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame

namespace CostStaticCanonicalAtomFrameAlignment

/-- Reverse a canonical semantic-atom frame alignment while retaining the
same common semantic quotient. -/
def symm
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    (alignment : CostStaticCanonicalAtomFrameAlignment left right leftFrame
      rightFrame) :
    CostStaticCanonicalAtomFrameAlignment right left rightFrame leftFrame where
  cospan := alignment.cospan.symm
  leftCovered := alignment.rightCovered
  rightCovered := alignment.leftCovered
  reifiedFrames_eq := by
    simpa only [CostStaticAtomKeyCospan.symm_reifyWith,
      CostStaticAtomKeyCospan.symm_leftSlot,
      CostStaticAtomKeyCospan.symm_rightSlot] using
      alignment.reifiedFrames_eq.symm

/-- Common-apex restoration of aligned canonical atom frames is exact. -/
theorem restoredFrames_eq
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    (alignment : CostStaticCanonicalAtomFrameAlignment left right leftFrame
      rightFrame)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        left.restorationSupport left.restorationAssignment availableDepth
        leftFrame =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        right.restorationSupport right.restorationAssignment availableDepth
        rightFrame := by
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt left
      alignment.cospan alignment.cospan.leftSlot
      alignment.cospan.leftCommutes availableDepth leftFrame
      alignment.leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt right
      alignment.cospan alignment.cospan.rightSlot
      alignment.cospan.rightCommutes availableDepth rightFrame
      alignment.rightCovered
  calc
    _ = ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          alignment.cospan.commonSupport alignment.cospan.commonAssignment
          availableDepth
          (alignment.cospan.reifyWith left.lookupAtom?
            alignment.cospan.leftSlot leftFrame) := leftFactor.symm
    _ = ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          alignment.cospan.commonSupport alignment.cospan.commonAssignment
          availableDepth
          (alignment.cospan.reifyWith right.lookupAtom?
            alignment.cospan.rightSlot rightFrame) := by
      exact congrArg
        (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          alignment.cospan.commonSupport alignment.cospan.commonAssignment
          availableDepth)
        alignment.reifiedFrames_eq
    _ = _ := rightFactor

end CostStaticCanonicalAtomFrameAlignment

/-! ## Canonical frames modulo common restoration

Exact equality of internal atom names is stronger than equality of the
compact meanings they denote.  In particular, a semantic ordering key may
tie on two distinct typed atoms whose restored patterns are equal.  The
following sibling of `CostStaticCanonicalAtomFrameAlignment` retains the
complete typed cospan, but asks the two common-apex frames to agree only after
the common supported assignment has been applied. -/

/-- Alignment of two canonical atom frames at their common restored meaning.

The premise is not equality of the endpoint evaluator results: it is an
equality inside the independently constructed common semantic namespace.
Both endpoint equalities are derived below from the two commuting cospan
legs. -/
structure CostStaticCanonicalAtomRestorationAlignment
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
    (availableDepth : Nat) (leftFrame rightFrame : Pattern) where
  cospan : CostStaticAtomKeyCospan
    (fun slot => (left.atomValue slot).key)
    (fun slot => (right.atomValue slot).key)
  leftCovered : forall name, name ∈ leftFrame.freeFvarNames ->
    exists slot, left.lookupAtom? name = some slot
  rightCovered : forall name, name ∈ rightFrame.freeFvarNames ->
    exists slot, right.lookupAtom? name = some slot
  commonRestorations_eq :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (cospan.reifyWith left.lookupAtom? cospan.leftSlot leftFrame) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment availableDepth
        (cospan.reifyWith right.lookupAtom? cospan.rightSlot rightFrame)

namespace CostStaticCanonicalAtomRestorationAlignment

/-- Reverse a canonical-frame restoration alignment at the same common
semantic apex. -/
def symm
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {availableDepth : Nat} {leftFrame rightFrame : Pattern}
    (alignment : CostStaticCanonicalAtomRestorationAlignment left right
      availableDepth leftFrame rightFrame) :
    CostStaticCanonicalAtomRestorationAlignment right left availableDepth
      rightFrame leftFrame where
  cospan := alignment.cospan.symm
  leftCovered := alignment.rightCovered
  rightCovered := alignment.leftCovered
  commonRestorations_eq := by
    simpa only [CostStaticAtomKeyCospan.symm_commonSupport,
      CostStaticAtomKeyCospan.symm_commonAssignment,
      CostStaticAtomKeyCospan.symm_reifyWith,
      CostStaticAtomKeyCospan.symm_leftSlot,
      CostStaticAtomKeyCospan.symm_rightSlot] using
      alignment.commonRestorations_eq.symm

/-- A common restored canonical frame descends to exact equality of the two
endpoint restorations.  Distinct internal atom identities remain retained in
the certificate even when their compact restored meanings coincide. -/
theorem restoredFrames_eq
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {availableDepth : Nat} {leftFrame rightFrame : Pattern}
    (alignment : CostStaticCanonicalAtomRestorationAlignment left right
      availableDepth leftFrame rightFrame) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        left.restorationSupport left.restorationAssignment availableDepth
        leftFrame =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        right.restorationSupport right.restorationAssignment availableDepth
        rightFrame := by
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt left
      alignment.cospan alignment.cospan.leftSlot
      alignment.cospan.leftCommutes availableDepth leftFrame
      alignment.leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt right
      alignment.cospan alignment.cospan.rightSlot
      alignment.cospan.rightCommutes availableDepth rightFrame
      alignment.rightCovered
  exact leftFactor.symm.trans
    (alignment.commonRestorations_eq.trans rightFactor)

end CostStaticCanonicalAtomRestorationAlignment

/-- Two local evaluator results factored through a common restored canonical
atom frame. -/
structure CostStaticCanonicalAtomRestorationEvaluationBridge
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {availableDepth : Nat} {leftFrame rightFrame : Pattern}
    (alignment : CostStaticCanonicalAtomRestorationAlignment left right
      availableDepth leftFrame rightFrame)
    (leftResult rightResult : Pattern) where
  leftFactors : leftResult =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      left.restorationSupport left.restorationAssignment availableDepth
      leftFrame
  rightFactors : rightResult =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      right.restorationSupport right.restorationAssignment availableDepth
      rightFrame

namespace CostStaticCanonicalAtomRestorationEvaluationBridge

/-- Reverse a common-restoration evaluation bridge. -/
def symm
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {availableDepth : Nat} {leftFrame rightFrame : Pattern}
    {alignment : CostStaticCanonicalAtomRestorationAlignment left right
      availableDepth leftFrame rightFrame}
    {leftResult rightResult : Pattern}
    (bridge : CostStaticCanonicalAtomRestorationEvaluationBridge alignment
      leftResult rightResult) :
    CostStaticCanonicalAtomRestorationEvaluationBridge alignment.symm
      rightResult leftResult where
  leftFactors := bridge.rightFactors
  rightFactors := bridge.leftFactors

/-- Exact evaluator agreement derived from the common restored semantic
apex. -/
theorem results_eq
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {availableDepth : Nat} {leftFrame rightFrame leftResult rightResult : Pattern}
    {alignment : CostStaticCanonicalAtomRestorationAlignment left right
      availableDepth leftFrame rightFrame}
    (bridge : CostStaticCanonicalAtomRestorationEvaluationBridge alignment
      leftResult rightResult) :
    leftResult = rightResult :=
  bridge.leftFactors.trans
    (alignment.restoredFrames_eq.trans bridge.rightFactors.symm)

end CostStaticCanonicalAtomRestorationEvaluationBridge

/-- Dependent package for an evaluation bridge whose canonical frames agree
after restoration at their common semantic apex. -/
structure PackedCostStaticCanonicalAtomRestorationEvaluationBridge
    (source : CIGSLT) (leftResult rightResult : Pattern) where
  leftColor : CostStaticColor
  rightColor : CostStaticColor
  targetFree : WellSorted.FreeTypeContext
  leftOccurrences : List CostRegionOccurrence
  rightOccurrences : List CostRegionOccurrence
  leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
    leftOccurrences
  rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
    rightOccurrences
  leftValues : TypedCostRegionBoundaryTable.Values source leftColor targetFree
    leftTable
  rightValues : TypedCostRegionBoundaryTable.Values source rightColor
    targetFree rightTable
  leftRoot : Pattern
  rightRoot : Pattern
  leftInventory : CostStaticParameterInventory source leftColor targetFree
    leftTable leftValues leftRoot
  rightInventory : CostStaticParameterInventory source rightColor targetFree
    rightTable rightValues rightRoot
  leftEnvironment : CostStaticAtomEnvironment source leftColor targetFree
    leftInventory
  rightEnvironment : CostStaticAtomEnvironment source rightColor targetFree
    rightInventory
  availableDepth : Nat
  leftFrame : Pattern
  rightFrame : Pattern
  alignment : CostStaticCanonicalAtomRestorationAlignment leftEnvironment
    rightEnvironment availableDepth leftFrame rightFrame
  bridge : CostStaticCanonicalAtomRestorationEvaluationBridge alignment
    leftResult rightResult

namespace PackedCostStaticCanonicalAtomRestorationEvaluationBridge

/-- Reverse a packed common-restoration evaluation bridge. -/
def symm
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (packed : PackedCostStaticCanonicalAtomRestorationEvaluationBridge source
      leftResult rightResult) :
    PackedCostStaticCanonicalAtomRestorationEvaluationBridge source rightResult
      leftResult where
  leftColor := packed.rightColor
  rightColor := packed.leftColor
  targetFree := packed.targetFree
  leftOccurrences := packed.rightOccurrences
  rightOccurrences := packed.leftOccurrences
  leftTable := packed.rightTable
  rightTable := packed.leftTable
  leftValues := packed.rightValues
  rightValues := packed.leftValues
  leftRoot := packed.rightRoot
  rightRoot := packed.leftRoot
  leftInventory := packed.rightInventory
  rightInventory := packed.leftInventory
  leftEnvironment := packed.rightEnvironment
  rightEnvironment := packed.leftEnvironment
  availableDepth := packed.availableDepth
  leftFrame := packed.rightFrame
  rightFrame := packed.leftFrame
  alignment := packed.alignment.symm
  bridge := packed.bridge.symm

/-- Package an already-constructed common-restoration evaluation bridge. -/
def ofBridge
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
    {leftEnvironment : CostStaticAtomEnvironment source leftColor targetFree
      leftInventory}
    {rightEnvironment : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {availableDepth : Nat}
    {leftFrame rightFrame leftResult rightResult : Pattern}
    {alignment : CostStaticCanonicalAtomRestorationAlignment leftEnvironment
      rightEnvironment availableDepth leftFrame rightFrame}
    (bridge : CostStaticCanonicalAtomRestorationEvaluationBridge alignment
      leftResult rightResult) :
    PackedCostStaticCanonicalAtomRestorationEvaluationBridge source leftResult
      rightResult where
  leftColor := leftColor
  rightColor := rightColor
  targetFree := targetFree
  leftOccurrences := leftOccurrences
  rightOccurrences := rightOccurrences
  leftTable := leftTable
  rightTable := rightTable
  leftValues := leftValues
  rightValues := rightValues
  leftRoot := leftRoot
  rightRoot := rightRoot
  leftInventory := leftInventory
  rightInventory := rightInventory
  leftEnvironment := leftEnvironment
  rightEnvironment := rightEnvironment
  availableDepth := availableDepth
  leftFrame := leftFrame
  rightFrame := rightFrame
  alignment := alignment
  bridge := bridge

/-- Exact evaluator equality remains derived after dependent packaging. -/
theorem results_eq
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (packed : PackedCostStaticCanonicalAtomRestorationEvaluationBridge source
      leftResult rightResult) :
    leftResult = rightResult :=
  packed.bridge.results_eq

end PackedCostStaticCanonicalAtomRestorationEvaluationBridge

/-- Two local evaluator results factored through aligned canonical atom
frames.  Result equality remains derived from the common semantic quotient. -/
structure CostStaticCanonicalAtomEvaluationBridge
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    (alignment : CostStaticCanonicalAtomFrameAlignment left right leftFrame
      rightFrame)
    (availableDepth : Nat) (leftResult rightResult : Pattern) where
  leftFactors : leftResult =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      left.restorationSupport left.restorationAssignment availableDepth
      leftFrame
  rightFactors : rightResult =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      right.restorationSupport right.restorationAssignment availableDepth
      rightFrame

namespace CostStaticCanonicalAtomEvaluationBridge

/-- Reverse a canonical semantic-atom evaluation bridge. -/
def symm
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    {alignment : CostStaticCanonicalAtomFrameAlignment left right leftFrame
      rightFrame}
    {availableDepth : Nat} {leftResult rightResult : Pattern}
    (bridge : CostStaticCanonicalAtomEvaluationBridge alignment availableDepth
      leftResult rightResult) :
    CostStaticCanonicalAtomEvaluationBridge alignment.symm availableDepth
      rightResult leftResult where
  leftFactors := bridge.rightFactors
  rightFactors := bridge.leftFactors

/-- Exact evaluator agreement derived from the canonical atom-frame square. -/
theorem results_eq
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
    {left : CostStaticAtomEnvironment source leftColor targetFree leftInventory}
    {right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame : Pattern}
    {alignment : CostStaticCanonicalAtomFrameAlignment left right leftFrame
      rightFrame}
    {availableDepth : Nat} {leftResult rightResult : Pattern}
    (bridge : CostStaticCanonicalAtomEvaluationBridge alignment availableDepth
      leftResult rightResult) :
    leftResult = rightResult :=
  bridge.leftFactors.trans
    ((alignment.restoredFrames_eq availableDepth).trans
      bridge.rightFactors.symm)

end CostStaticCanonicalAtomEvaluationBridge

/-- Existential package for a canonical atom-frame evaluator bridge.  The
endpoint inventories and environments remain available for occurrence-level
audits after dependent indices have been hidden. -/
structure PackedCostStaticCanonicalAtomEvaluationBridge
    (source : CIGSLT) (leftResult rightResult : Pattern) where
  leftColor : CostStaticColor
  rightColor : CostStaticColor
  targetFree : WellSorted.FreeTypeContext
  leftOccurrences : List CostRegionOccurrence
  rightOccurrences : List CostRegionOccurrence
  leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
    leftOccurrences
  rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
    rightOccurrences
  leftValues : TypedCostRegionBoundaryTable.Values source leftColor targetFree
    leftTable
  rightValues : TypedCostRegionBoundaryTable.Values source rightColor
    targetFree rightTable
  leftRoot : Pattern
  rightRoot : Pattern
  leftInventory : CostStaticParameterInventory source leftColor targetFree
    leftTable leftValues leftRoot
  rightInventory : CostStaticParameterInventory source rightColor targetFree
    rightTable rightValues rightRoot
  leftEnvironment : CostStaticAtomEnvironment source leftColor targetFree
    leftInventory
  rightEnvironment : CostStaticAtomEnvironment source rightColor targetFree
    rightInventory
  leftFrame : Pattern
  rightFrame : Pattern
  alignment : CostStaticCanonicalAtomFrameAlignment leftEnvironment
    rightEnvironment leftFrame rightFrame
  availableDepth : Nat
  bridge : CostStaticCanonicalAtomEvaluationBridge alignment availableDepth
    leftResult rightResult

namespace PackedCostStaticCanonicalAtomEvaluationBridge

/-- Reverse a packed canonical semantic-atom evaluation bridge. -/
def symm
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (packed : PackedCostStaticCanonicalAtomEvaluationBridge source leftResult
      rightResult) :
    PackedCostStaticCanonicalAtomEvaluationBridge source rightResult
      leftResult where
  leftColor := packed.rightColor
  rightColor := packed.leftColor
  targetFree := packed.targetFree
  leftOccurrences := packed.rightOccurrences
  rightOccurrences := packed.leftOccurrences
  leftTable := packed.rightTable
  rightTable := packed.leftTable
  leftValues := packed.rightValues
  rightValues := packed.leftValues
  leftRoot := packed.rightRoot
  rightRoot := packed.leftRoot
  leftInventory := packed.rightInventory
  rightInventory := packed.leftInventory
  leftEnvironment := packed.rightEnvironment
  rightEnvironment := packed.leftEnvironment
  leftFrame := packed.rightFrame
  rightFrame := packed.leftFrame
  alignment := packed.alignment.symm
  availableDepth := packed.availableDepth
  bridge := packed.bridge.symm

/-- Package an already-constructed canonical atom-frame bridge. -/
def ofBridge
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
    {leftEnvironment : CostStaticAtomEnvironment source leftColor targetFree
      leftInventory}
    {rightEnvironment : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory}
    {leftFrame rightFrame leftResult rightResult : Pattern}
    {alignment : CostStaticCanonicalAtomFrameAlignment leftEnvironment
      rightEnvironment leftFrame rightFrame}
    {availableDepth : Nat}
    (bridge : CostStaticCanonicalAtomEvaluationBridge alignment availableDepth
      leftResult rightResult) :
    PackedCostStaticCanonicalAtomEvaluationBridge source leftResult
      rightResult where
  leftColor := leftColor
  rightColor := rightColor
  targetFree := targetFree
  leftOccurrences := leftOccurrences
  rightOccurrences := rightOccurrences
  leftTable := leftTable
  rightTable := rightTable
  leftValues := leftValues
  rightValues := rightValues
  leftRoot := leftRoot
  rightRoot := rightRoot
  leftInventory := leftInventory
  rightInventory := rightInventory
  leftEnvironment := leftEnvironment
  rightEnvironment := rightEnvironment
  leftFrame := leftFrame
  rightFrame := rightFrame
  alignment := alignment
  availableDepth := availableDepth
  bridge := bridge

/-- Exact evaluator equality remains derived after dependent packaging. -/
theorem results_eq
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (packed : PackedCostStaticCanonicalAtomEvaluationBridge source leftResult
      rightResult) :
    leftResult = rightResult :=
  packed.bridge.results_eq

end PackedCostStaticCanonicalAtomEvaluationBridge

/-! ## Exact quotient canaries -/

private def zeroAtomKey : CostStaticAtomKey where
  sourceType := .base "Name"
  sourceSupport := []
  targetType := .base "Name"
  targetSupport := []
  normal := .fvar "0"

private def aAtomKey : CostStaticAtomKey where
  sourceType := .base "Name"
  sourceSupport := []
  targetType := .base "Name"
  targetSupport := []
  normal := .fvar "a"

/-- Equal meanings from independently positioned endpoint inventories land
in exactly the same common semantic slot. -/
example :
    (CostStaticAtomKeyCospan.ofFunctions
      (fun slot : Fin 2 => [zeroAtomKey, aAtomKey].get slot)
      (fun slot : Fin 2 => [aAtomKey, zeroAtomKey].get slot)).leftSlot
        ⟨0, by decide⟩ =
    (CostStaticAtomKeyCospan.ofFunctions
      (fun slot : Fin 2 => [zeroAtomKey, aAtomKey].get slot)
      (fun slot : Fin 2 => [aAtomKey, zeroAtomKey].get slot)).rightSlot
        ⟨1, by decide⟩ := by
  apply ((CostStaticAtomKeyCospan.ofFunctions
    (fun slot : Fin 2 => [zeroAtomKey, aAtomKey].get slot)
    (fun slot : Fin 2 => [aAtomKey, zeroAtomKey].get slot)).crossExtensional
      ⟨0, by decide⟩ ⟨1, by decide⟩).mpr
  rfl

/-- Distinct normalized meanings remain distinct common semantic slots. -/
example :
    (CostStaticAtomKeyCospan.ofFunctions
      (fun _ : Fin 1 => zeroAtomKey)
      (fun _ : Fin 1 => aAtomKey)).leftSlot ⟨0, by decide⟩ ≠
    (CostStaticAtomKeyCospan.ofFunctions
      (fun _ : Fin 1 => zeroAtomKey)
      (fun _ : Fin 1 => aAtomKey)).rightSlot ⟨0, by decide⟩ := by
  intro equalSlot
  have equalKey := ((CostStaticAtomKeyCospan.ofFunctions
    (fun _ : Fin 1 => zeroAtomKey)
    (fun _ : Fin 1 => aAtomKey)).crossExtensional
      ⟨0, by decide⟩ ⟨0, by decide⟩).mp
      equalSlot
  exact (by decide : zeroAtomKey ≠ aAtomKey) equalKey

end Mettapedia.GSLT.LanguageDef
