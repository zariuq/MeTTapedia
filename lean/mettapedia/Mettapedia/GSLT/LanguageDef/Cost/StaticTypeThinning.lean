import Mettapedia.GSLT.LanguageDef.Cost.StaticTypeImage
import Mettapedia.GSLT.LanguageDef.ContextRenamingTyping

/-!
# Binder insertion in an exact static type image

The target context is partitioned by executable type decoding. Retained
positions are exact mapped source types; rejected positions remain explicit
foreign binders. Pattern action reuses the shared ambient-renaming traversal.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism WellSorted

inductive CostStaticTypeThinning (theory : IGSLT)
    (color : CostStaticColor) : List TypeExpr → List TypeExpr → Type where
  | nil : CostStaticTypeThinning theory color [] []
  | mapped {sourceBound targetBound : List TypeExpr}
      (sourceType : TypeExpr)
      (tail : CostStaticTypeThinning theory color sourceBound targetBound) :
      CostStaticTypeThinning theory color (sourceType :: sourceBound)
        (mapTypeExpr (color.symbolsOf theory) sourceType :: targetBound)
  | foreign {sourceBound targetBound : List TypeExpr}
      (targetType : TypeExpr)
      (rejected : CostStaticTypeImage.decode theory color targetType = none)
      (tail : CostStaticTypeThinning theory color sourceBound targetBound) :
      CostStaticTypeThinning theory color sourceBound
        (targetType :: targetBound)

namespace CostStaticTypeThinning

/-- The source binder context obtained by filtering a target context through
one exact static Cost image.  Foreign entries are omitted but remain recorded
in `ofTargetThinning`; this computation alone is never used as evidence. -/
def sourceContextOfTarget (theory : IGSLT) (color : CostStaticColor)
    (targetBound : List TypeExpr) : List TypeExpr :=
  match targetBound with
  | [] => []
  | targetType :: targetBound =>
      match CostStaticTypeImage.decode theory color targetType with
      | none => sourceContextOfTarget theory color targetBound
      | some sourceType =>
          sourceType :: sourceContextOfTarget theory color targetBound
termination_by targetBound.length

/-- Proof-relevant companion to `sourceContextOfTarget`.  It records every
retained and skipped target position in the same left-to-right traversal. -/
def ofTargetThinning (theory : IGSLT) (color : CostStaticColor)
    (targetBound : List TypeExpr) :
    CostStaticTypeThinning theory color
      (sourceContextOfTarget theory color targetBound) targetBound := by
  match targetBound with
  | [] => simpa [sourceContextOfTarget] using
      (CostStaticTypeThinning.nil (theory := theory) (color := color))
  | targetType :: targetBound =>
      cases decoded : CostStaticTypeImage.decode theory color targetType with
      | none =>
          simpa [sourceContextOfTarget, decoded] using
            CostStaticTypeThinning.foreign targetType decoded
              (ofTargetThinning theory color targetBound)
      | some sourceType =>
          have mapped :
              mapTypeExpr (color.symbolsOf theory) sourceType = targetType :=
            CostStaticTypeImage.mapTypeExpr_decode theory color decoded
          subst targetType
          simpa [sourceContextOfTarget] using
            CostStaticTypeThinning.mapped sourceType
              (ofTargetThinning theory color targetBound)
termination_by targetBound.length

/-- Extend a static binder thinning by an ordered block of freshly introduced
source binders and their exact target images.  This is the intrinsic context
action used by multi-binder region plans. -/
def prependMapped {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr} :
    (arity : Nat) → (sourceType : TypeExpr) →
    (tail : CostStaticTypeThinning theory color sourceBound targetBound) →
    CostStaticTypeThinning theory color
      (List.replicate arity sourceType ++ sourceBound)
      (List.replicate arity (mapTypeExpr (color.symbolsOf theory) sourceType) ++
        targetBound)
  | 0, _sourceType, tail => tail
  | Nat.succ arity, sourceType, tail =>
      CostStaticTypeThinning.mapped sourceType
        (prependMapped arity sourceType tail)

/-- Filtering a context already wholly in the selected static image recovers
the authored source context exactly. -/
@[simp]
theorem sourceContextOfTarget_map (theory : IGSLT)
    (color : CostStaticColor) (sourceBound : List TypeExpr) :
    sourceContextOfTarget theory color
      (sourceBound.map (mapTypeExpr (color.symbolsOf theory))) = sourceBound := by
  induction sourceBound with
  | nil => simp [sourceContextOfTarget]
  | cons sourceType sourceBound inductionHypothesis =>
      simp [sourceContextOfTarget, inductionHypothesis]

/-- The proof-relevant thinning computes exactly the same selected-colour
source context as the executable target-context filter. -/
@[simp]
theorem sourceContextOfTarget_eq_of_thinning
    {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    sourceContextOfTarget theory color targetBound = sourceBound := by
  induction thinning with
  | nil => simp [sourceContextOfTarget]
  | mapped sourceType tail inductionHypothesis =>
      simp [sourceContextOfTarget, inductionHypothesis]
  | foreign targetType rejected tail inductionHypothesis =>
      simp [sourceContextOfTarget, rejected, inductionHypothesis]


/-- The proof-relevant thinning of a fixed target context into one static
colour is unique.  Decoding decides whether each target binder is retained or
foreign; the constructors retain the resulting evidence rather than adding a
second choice. -/
theorem all_eq {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (left right : CostStaticTypeThinning theory color sourceBound
      targetBound) :
    left = right := by
  induction left with
  | nil =>
      cases right
      rfl
  | mapped sourceType tail inductionHypothesis =>
      cases right with
      | mapped sourceType' tail' =>
          congr
          exact inductionHypothesis tail'
      | foreign targetType rejected tail' =>
          simp [CostStaticTypeImage.decode_mapTypeExpr] at rejected
  | foreign targetType rejected tail inductionHypothesis =>
      cases right with
      | mapped sourceType tail' =>
          simp [CostStaticTypeImage.decode_mapTypeExpr] at rejected
      | foreign targetType' rejected' tail' =>
          congr
          exact inductionHypothesis tail'

instance {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr} :
    Subsingleton (CostStaticTypeThinning theory color sourceBound
      targetBound) :=
  ⟨all_eq⟩

/-- Embed a decoded source-context index into its original target position.
The function is total on naturals, while the lookup theorems below give its
meaning precisely on in-range source indices. -/
def toTargetIndex {theory : IGSLT} {color : CostStaticColor} :
    {sourceBound targetBound : List TypeExpr} →
      CostStaticTypeThinning theory color sourceBound targetBound → Nat → Nat
  | [], [], .nil, index => index
  | _ :: _, _ :: _, .mapped _ _, 0 => 0
  | _ :: _, _ :: _, .mapped _ tail, index + 1 =>
      tail.toTargetIndex index + 1
  | _, _ :: _, .foreign _ _ tail, index =>
      tail.toTargetIndex index + 1

/-- Partially contract a target-context index to the decoded source context.
Foreign binder positions return `none`; no neighboring image entry is used as
a fallback. -/
def toSourceIndex? {theory : IGSLT} {color : CostStaticColor} :
    {sourceBound targetBound : List TypeExpr} →
      CostStaticTypeThinning theory color sourceBound targetBound →
      Nat → Option Nat
  | [], [], .nil, _ => none
  | _ :: _, _ :: _, .mapped _ _, 0 => some 0
  | _ :: _, _ :: _, .mapped _ tail, index + 1 =>
      (tail.toSourceIndex? index).map Nat.succ
  | _, _ :: _, .foreign _ _ _, 0 => none
  | _, _ :: _, .foreign _ _ tail, index + 1 =>
      tail.toSourceIndex? index


/-- Every in-range decoded source entry embeds at an equal mapped target
type. -/
theorem lookup_toTargetIndex {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    {index : Nat} {sourceType : TypeExpr}
    (lookup : sourceBound[index]? = some sourceType) :
    targetBound[thinning.toTargetIndex index]? =
      some (mapTypeExpr (color.symbolsOf theory) sourceType) := by
  induction thinning generalizing index sourceType with
  | nil => simp at lookup
  | mapped head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp at lookup
          subst sourceType
          rfl
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          simpa [toTargetIndex] using inductionHypothesis lookup
  | foreign targetType rejected tail inductionHypothesis =>
      simpa [toTargetIndex] using inductionHypothesis lookup

/-- Foreign binder insertion preserves the order of every source position. -/
theorem toTargetIndex_strictMono {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    StrictMono thinning.toTargetIndex := by
  intro left right less
  induction thinning generalizing left right with
  | nil => exact less
  | mapped sourceType tail ih =>
      cases left with
      | zero =>
          cases right with
          | zero => omega
          | succ right => simp [toTargetIndex]
      | succ left =>
          cases right with
          | zero => omega
          | succ right =>
              simp only [toTargetIndex]
              exact Nat.add_lt_add_right (ih (by omega)) 1
  | foreign targetType rejected tail ih =>
      simpa only [toTargetIndex] using Nat.add_lt_add_right (ih less) 1

theorem toTargetIndex_injective {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    Function.Injective thinning.toTargetIndex := thinning.toTargetIndex_strictMono.injective

/-- Recovering the position of an embedded in-range variable is exact. -/
theorem toSourceIndex?_toTargetIndex {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    {index : Nat} (inRange : index < sourceBound.length) :
    thinning.toSourceIndex? (thinning.toTargetIndex index) = some index := by
  induction thinning generalizing index with
  | nil => simp at inRange
  | mapped sourceType tail ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have smaller : index < _ := Nat.lt_of_succ_lt_succ inRange
          simpa [toSourceIndex?, toTargetIndex] using congrArg (Option.map Nat.succ) (ih smaller)
  | foreign targetType rejected tail ih =>
      simpa [toSourceIndex?, toTargetIndex] using ih inRange

/-- Successful contraction restores the original target occurrence, not
another occurrence with an equal type. -/
theorem toTargetIndex_toSourceIndex? {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    {targetIndex sourceIndex : Nat}
    (found : thinning.toSourceIndex? targetIndex = some sourceIndex) :
    thinning.toTargetIndex sourceIndex = targetIndex := by
  induction thinning generalizing targetIndex sourceIndex with
  | nil => simp [toSourceIndex?] at found
  | mapped type tail ih =>
      cases targetIndex with
      | zero =>
          simp only [toSourceIndex?, Option.some.injEq] at found
          subst sourceIndex
          rfl
      | succ targetIndex =>
          simp only [toSourceIndex?] at found
          obtain ⟨index, lookup, rfl⟩ := Option.map_eq_some_iff.mp found
          simpa only [toTargetIndex] using congrArg Nat.succ (ih lookup)
  | foreign type rejected tail ih =>
      cases targetIndex with
      | zero => simp [toSourceIndex?] at found
      | succ targetIndex =>
          simp only [toSourceIndex?] at found
          simpa only [toTargetIndex] using congrArg Nat.succ (ih found)

/-- Distinct available source occurrences remain distinct target positions. -/
theorem toTargetIndex_injective_on {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    {left right : Nat} (leftRange : left < sourceBound.length)
    (rightRange : right < sourceBound.length)
    (equal : thinning.toTargetIndex left = thinning.toTargetIndex right) : left = right := by
  have recovered := congrArg thinning.toSourceIndex? equal
  simpa [thinning.toSourceIndex?_toTargetIndex leftRange,
    thinning.toSourceIndex?_toTargetIndex rightRange] using recovered

/-- Exact image lookup supplies the common typed ambient-renaming interface. -/
theorem preservesBoundTypes {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    PreservesBoundTypes (sourceBound.map (mapTypeExpr (color.symbolsOf theory)))
      targetBound thinning.toTargetIndex := by
  intro index type lookup
  rw [List.getElem?_map] at lookup
  cases original : sourceBound[index]? with
  | none => simp [original] at lookup
  | some sourceType =>
      simp only [original, Option.map_some, Option.some.injEq] at lookup
      simpa [lookup] using thinning.lookup_toTargetIndex original

/-- Embed ambient source positions after static symbol transport. The local
binder prefix, free-variable assignment and authored row witnesses are kept. -/
theorem hasType_renameAmbient {theory : IGSLT} {color : CostStaticColor}
    {sourceBound targetBound inner : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    {language : LanguageDef} {free : FreeTypeContext} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free
      (inner ++ sourceBound.map (mapTypeExpr (color.symbolsOf theory))) pattern type) :
    HasType language free (inner ++ targetBound)
      (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex inner.length pattern) type :=
  typed.renameAmbientBVarsAt thinning.toTargetIndex thinning.preservesBoundTypes

end CostStaticTypeThinning

namespace CostStaticTypeThinning.Controls

/-- Two equal source types retain different positions around two apparatus
binders. Equality of type values does not select the first occurrence. -/
def repeated (theory : IGSLT) (color : CostStaticColor) (type : TypeExpr) :
    CostStaticTypeThinning theory color [type, type]
      [.base costSignatureSortName, mapTypeExpr (color.symbolsOf theory) type,
        .base costKeySortName, mapTypeExpr (color.symbolsOf theory) type] :=
  .foreign _ (CostStaticTypeImage.decode_signature theory color)
    (.mapped type (.foreign _ (CostStaticTypeImage.decode_key theory color) (.mapped type .nil)))

theorem repeated_positions (theory : IGSLT) (color : CostStaticColor) (type : TypeExpr) :
    (repeated theory color type).toTargetIndex 0 = 1 ∧
    (repeated theory color type).toTargetIndex 1 = 3 := by
  constructor <;> rfl

theorem apparatus_positions_rejected (theory : IGSLT) (color : CostStaticColor) (type : TypeExpr) :
    (repeated theory color type).toSourceIndex? 0 = none ∧
    (repeated theory color type).toSourceIndex? 2 = none := by
  constructor <;> rfl

def nested : Pattern :=
  .lambda none (.collection .hashBag [.bvar 0, .bvar 1, .bvar 2] none)

theorem nested_reindexed (theory : IGSLT) (color : CostStaticColor) (type : TypeExpr) :
    ContextSubstitution.renameAmbientBVarsAt (repeated theory color type).toTargetIndex 0 nested =
      .lambda none (.collection .hashBag [.bvar 0, .bvar 2, .bvar 4] none) := by
  simp [nested, ContextSubstitution.renameAmbientBVarsAt, repeated, toTargetIndex]

/-- Actual typing under one local binder and two repeated ambient types. -/
theorem nested_reindexed_typed (theory : IGSLT) (color : CostStaticColor) (type : TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) :
    HasType language free
      [.base costSignatureSortName, mapTypeExpr (color.symbolsOf theory) type,
        .base costKeySortName, mapTypeExpr (color.symbolsOf theory) type]
      (.lambda none (.collection .hashBag [.bvar 0, .bvar 2, .bvar 4] none))
      (.arrow (mapTypeExpr (color.symbolsOf theory) type)
        (.collection .hashBag (mapTypeExpr (color.symbolsOf theory) type))) := by
  have typed : HasType language free
      ([type, type].map (mapTypeExpr (color.symbolsOf theory))) nested
      (.arrow (mapTypeExpr (color.symbolsOf theory) type)
        (.collection .hashBag (mapTypeExpr (color.symbolsOf theory) type))) :=
    .lambda (.collection (.cons (.bvar rfl) (.cons (.bvar rfl) (.cons (.bvar rfl) (.nil _ _)))))
  simpa only [List.nil_append, List.length_nil, nested_reindexed] using
    (repeated theory color type).hasType_renameAmbient (inner := []) typed

end CostStaticTypeThinning.Controls
end Mettapedia.GSLT.LanguageDef
