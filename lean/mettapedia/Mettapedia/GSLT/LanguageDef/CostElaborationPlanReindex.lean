import Mettapedia.GSLT.LanguageDef.CostElaborationConservative

/-!
# Reindexing executable Cost region plans

An admitted Cost elaboration retains the exact constructor declaration,
static colour, binder thinning, collection fibre, and boundary certificate
selected by its source presentation.  Conservative Cost arrows transport
that evidence structurally.  The target-side executable checks are derived
as theorems; they never select a replacement plan.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace WellSorted

/-- Objectness of an application exposes objectness of its argument spine. -/
theorem objectArguments_of_objectApplication {constructor : String}
    {arguments : List Pattern}
    (object : isObjectPattern (.apply constructor arguments) = true) :
    isObjectPatternList arguments = true := by
  simpa [isObjectPattern] using object

/-- Objectness of a lambda is exactly objectness of its body. -/
theorem objectBody_of_objectLambda {binder : Option String} {body : Pattern}
    (object : isObjectPattern (.lambda binder body) = true) :
    isObjectPattern body = true := by
  simpa [isObjectPattern] using object

/-- Objectness of a multiple lambda is exactly objectness of its body. -/
theorem objectBody_of_objectMultiLambda {arity : Nat}
    {binders : List String} {body : Pattern}
    (object : isObjectPattern (.multiLambda arity binders body) = true) :
    isObjectPattern body = true := by
  simpa [isObjectPattern] using object

/-- An admitted collection has a closed tail and an object element spine. -/
theorem objectElements_of_objectCollection {collectionType : CollType}
    {elements : List Pattern} {rest : Option String}
    (object : isObjectPattern
      (.collection collectionType elements rest) = true) :
    isObjectPatternList elements = true := by
  have parts : rest.isNone = true ∧ isObjectPatternList elements = true := by
    simpa [isObjectPattern] using object
  exact parts.2

/-- Split objectness of an ordered spine at its head. -/
theorem objectList_cons {head : Pattern} {tail : List Pattern}
    (objects : isObjectPatternList (head :: tail) = true) :
    isObjectPattern head = true ∧ isObjectPatternList tail = true := by
  simpa [isObjectPatternList] using objects

end WellSorted

namespace CostStaticRegionPlan

/-- Transport only the dependent indices of a retained region plan.  Once
the contexts are identified, the binder thinning is forced by decoding and
therefore equal by proof-relevant thinning uniqueness. -/
def reindex {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {pattern₁ pattern₂ : Pattern}
    {sourceType₁ sourceType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (sourceType : sourceType₁ = sourceType₂)
    (plan : CostStaticRegionPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ pattern₁ sourceType₁) :
    CostStaticRegionPlan source color targetFree sourceBound₂ targetBound₂
      thinning₂ available₂ outer₂ pattern₂ sourceType₂ := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst pattern₂
  subst sourceType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  exact plan

/-- Dependent index transport does not alter the ordered occurrence
projection of a retained region plan. -/
theorem reindex_occurrences {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {pattern₁ pattern₂ : Pattern}
    {sourceType₁ sourceType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (sourceType : sourceType₁ = sourceType₂)
    (plan : CostStaticRegionPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ pattern₁ sourceType₁) :
    (reindex (thinning₂ := thinning₂) sourceBound targetBound available
      outer pattern sourceType plan).occurrences = plan.occurrences := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst pattern₂
  subst sourceType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  simp [reindex]

/-- Dependent index transport leaves the retained boundary certificates in
their original occurrence slots. -/
theorem reindex_boundaryTable {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {pattern₁ pattern₂ : Pattern}
    {sourceType₁ sourceType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (sourceType : sourceType₁ = sourceType₂)
    (plan : CostStaticRegionPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ pattern₁
      sourceType₁) :
    TypedCostRegionBoundaryTable.cast
        (reindex_occurrences (thinning₂ := thinning₂) sourceBound
          targetBound available outer pattern sourceType plan)
        (reindex (thinning₂ := thinning₂) sourceBound targetBound available
          outer pattern sourceType plan).boundaryTable =
      plan.boundaryTable := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst pattern₂
  subst sourceType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  simp [reindex]

/-- Region-plan index transport is equality in the total boundary-packet
space. -/
theorem reindex_boundaryPacket {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {pattern₁ pattern₂ : Pattern}
    {sourceType₁ sourceType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (sourceType : sourceType₁ = sourceType₂)
    (plan : CostStaticRegionPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ pattern₁
      sourceType₁) :
    (reindex (thinning₂ := thinning₂) sourceBound targetBound available
      outer pattern sourceType plan).boundaryPacket = plan.boundaryPacket := by
  apply TypedCostRegionBoundaryPacket.ext_of_cast_eq
    (reindex_occurrences (thinning₂ := thinning₂) sourceBound
      targetBound available outer pattern sourceType plan)
  exact reindex_boundaryTable (thinning₂ := thinning₂) sourceBound
    targetBound available outer pattern sourceType plan

end CostStaticRegionPlan

namespace CostStaticArgumentPlan

/-- Transport the dependent indices of an ordered constructor-argument
plan.  The sequence and occurrence order are retained exactly. -/
def reindex {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {wireName₁ wireName₂ : String}
    {before₁ before₂ arguments₁ arguments₂ : List Pattern}
    {parameters₁ parameters₂ : List TermParam}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (wireName : wireName₁ = wireName₂)
    (before : before₁ = before₂) (arguments : arguments₁ = arguments₂)
    (parameters : parameters₁ = parameters₂)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ wireName₁ before₁ arguments₁
      parameters₁) :
    CostStaticArgumentPlan source color targetFree sourceBound₂ targetBound₂
      thinning₂ available₂ outer₂ wireName₂ before₂ arguments₂ parameters₂ := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst wireName₂
  subst before₂
  subst arguments₂
  subst parameters₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  exact plan

/-- Dependent index transport preserves an argument plan's occurrence
sequence. -/
theorem reindex_occurrences {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {wireName₁ wireName₂ : String}
    {before₁ before₂ arguments₁ arguments₂ : List Pattern}
    {parameters₁ parameters₂ : List TermParam}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (wireName : wireName₁ = wireName₂)
    (before : before₁ = before₂) (arguments : arguments₁ = arguments₂)
    (parameters : parameters₁ = parameters₂)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ wireName₁ before₁
      arguments₁ parameters₁) :
    (reindex (thinning₂ := thinning₂) sourceBound targetBound available
      outer wireName before arguments parameters plan).occurrences =
      plan.occurrences := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst wireName₂
  subst before₂
  subst arguments₂
  subst parameters₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  simp [reindex]

/-- Argument-plan index transport preserves its exact certificate table. -/
theorem reindex_boundaryTable {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {wireName₁ wireName₂ : String}
    {before₁ before₂ arguments₁ arguments₂ : List Pattern}
    {parameters₁ parameters₂ : List TermParam}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (wireName : wireName₁ = wireName₂)
    (before : before₁ = before₂) (arguments : arguments₁ = arguments₂)
    (parameters : parameters₁ = parameters₂)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ wireName₁ before₁
      arguments₁ parameters₁) :
    TypedCostRegionBoundaryTable.cast
        (reindex_occurrences (thinning₂ := thinning₂) sourceBound
          targetBound available outer wireName before arguments parameters plan)
        (reindex (thinning₂ := thinning₂) sourceBound targetBound available
          outer wireName before arguments parameters plan).boundaryTable =
      plan.boundaryTable := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst wireName₂
  subst before₂
  subst arguments₂
  subst parameters₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  simp [reindex]

/-- Argument-plan index transport is equality in the total boundary-packet
space. -/
theorem reindex_boundaryPacket {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {wireName₁ wireName₂ : String}
    {before₁ before₂ arguments₁ arguments₂ : List Pattern}
    {parameters₁ parameters₂ : List TermParam}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (wireName : wireName₁ = wireName₂)
    (before : before₁ = before₂) (arguments : arguments₁ = arguments₂)
    (parameters : parameters₁ = parameters₂)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ wireName₁ before₁
      arguments₁ parameters₁) :
    (reindex (thinning₂ := thinning₂) sourceBound targetBound available
      outer wireName before arguments parameters plan).boundaryPacket =
      plan.boundaryPacket := by
  apply TypedCostRegionBoundaryPacket.ext_of_cast_eq
    (reindex_occurrences (thinning₂ := thinning₂) sourceBound
      targetBound available outer wireName before arguments parameters plan)
  exact reindex_boundaryTable (thinning₂ := thinning₂) sourceBound
    targetBound available outer wireName before arguments parameters plan

end CostStaticArgumentPlan

namespace CostStaticElementPlan

/-- Transport the dependent indices of an ordered homogeneous-element plan. -/
def reindex {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {collectionType₁ collectionType₂ : CollType}
    {before₁ before₂ elements₁ elements₂ : List Pattern}
    {rest₁ rest₂ : Option String} {sourceElementType₁ sourceElementType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂)
    (collectionType : collectionType₁ = collectionType₂)
    (before : before₁ = before₂) (elements : elements₁ = elements₂)
    (rest : rest₁ = rest₂)
    (sourceElementType : sourceElementType₁ = sourceElementType₂)
    (plan : CostStaticElementPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ collectionType₁ before₁
      elements₁ rest₁ sourceElementType₁) :
    CostStaticElementPlan source color targetFree sourceBound₂ targetBound₂
      thinning₂ available₂ outer₂ collectionType₂ before₂ elements₂ rest₂
      sourceElementType₂ := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst collectionType₂
  subst before₂
  subst elements₂
  subst rest₂
  subst sourceElementType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  exact plan

/-- Dependent index transport preserves a collection-element plan's
occurrence sequence. -/
theorem reindex_occurrences {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext}
    {collectionType₁ collectionType₂ : CollType}
    {before₁ before₂ elements₁ elements₂ : List Pattern}
    {rest₁ rest₂ : Option String}
    {sourceElementType₁ sourceElementType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂)
    (collectionType : collectionType₁ = collectionType₂)
    (before : before₁ = before₂) (elements : elements₁ = elements₂)
    (rest : rest₁ = rest₂)
    (sourceElementType : sourceElementType₁ = sourceElementType₂)
    (plan : CostStaticElementPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ collectionType₁
      before₁ elements₁ rest₁ sourceElementType₁) :
    (reindex (thinning₂ := thinning₂) sourceBound targetBound available
      outer collectionType before elements rest sourceElementType plan).occurrences =
      plan.occurrences := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst collectionType₂
  subst before₂
  subst elements₂
  subst rest₂
  subst sourceElementType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  simp [reindex]

/-- Collection-element index transport preserves its exact certificate
table. -/
theorem reindex_boundaryTable {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext}
    {collectionType₁ collectionType₂ : CollType}
    {before₁ before₂ elements₁ elements₂ : List Pattern}
    {rest₁ rest₂ : Option String}
    {sourceElementType₁ sourceElementType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂)
    (collectionType : collectionType₁ = collectionType₂)
    (before : before₁ = before₂) (elements : elements₁ = elements₂)
    (rest : rest₁ = rest₂)
    (sourceElementType : sourceElementType₁ = sourceElementType₂)
    (plan : CostStaticElementPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ collectionType₁
      before₁ elements₁ rest₁ sourceElementType₁) :
    TypedCostRegionBoundaryTable.cast
        (reindex_occurrences (thinning₂ := thinning₂) sourceBound
          targetBound available outer collectionType before elements rest
          sourceElementType plan)
        (reindex (thinning₂ := thinning₂) sourceBound targetBound available
          outer collectionType before elements rest sourceElementType
          plan).boundaryTable =
      plan.boundaryTable := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst collectionType₂
  subst before₂
  subst elements₂
  subst rest₂
  subst sourceElementType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  simp [reindex]

/-- Collection-element index transport is equality in the total
boundary-packet space. -/
theorem reindex_boundaryPacket {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext}
    {collectionType₁ collectionType₂ : CollType}
    {before₁ before₂ elements₁ elements₂ : List Pattern}
    {rest₁ rest₂ : Option String}
    {sourceElementType₁ sourceElementType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂)
    (collectionType : collectionType₁ = collectionType₂)
    (before : before₁ = before₂) (elements : elements₁ = elements₂)
    (rest : rest₁ = rest₂)
    (sourceElementType : sourceElementType₁ = sourceElementType₂)
    (plan : CostStaticElementPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ collectionType₁
      before₁ elements₁ rest₁ sourceElementType₁) :
    (reindex (thinning₂ := thinning₂) sourceBound targetBound available
      outer collectionType before elements rest sourceElementType
      plan).boundaryPacket = plan.boundaryPacket := by
  apply TypedCostRegionBoundaryPacket.ext_of_cast_eq
    (reindex_occurrences (thinning₂ := thinning₂) sourceBound
      targetBound available outer collectionType before elements rest
      sourceElementType plan)
  exact reindex_boundaryTable (thinning₂ := thinning₂) sourceBound
    targetBound available outer collectionType before elements rest
    sourceElementType plan

end CostStaticElementPlan

/- The three plan families are mutually recursive.  Objectness evidence is
threaded through the recursion because collection-candidate preservation is
sound on admitted object terms, not on arbitrary schema syntax. -/
mutual
  def mapCostStaticRegionPlan {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {targetAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning targetAvailable outer pattern sourceType)
      (object : WellSorted.isObjectPattern pattern = true) :
      CostStaticRegionPlan target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (sourceBound.map
          (mapTypeExpr morphism.underlying.structural.structural.symbols))
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (thinning.map morphism color)
        (targetAvailable.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (CIGSLT.mapOneHoleContext
          morphism.costWholeStructural.symbols outer)
        (mapPattern morphism.costWholeStructural.symbols pattern)
        (mapTypeExpr
          morphism.underlying.structural.structural.symbols sourceType) := by
    cases plan with
    | @bvar sourceBound targetBound targetAvailable thinning outer targetIndex
        sourceType sourceIndex lookup correspondence availableScope =>
        apply CostStaticRegionPlan.bvar sourceIndex
        · simpa using congrArg
            (Option.map
              (mapTypeExpr
                morphism.underlying.structural.structural.symbols)) lookup
        · rw [CostStaticBinderThinning.toSourceIndex?_map]
          exact correspondence
        · rw [CostStaticBinderThinning.sourceContextOfTarget_natural]
          simpa using availableScope
    | @fvar sourceBound targetBound sourceAvailable thinning outer name
        sourceType lookup =>
        apply CostStaticRegionPlan.fvar
        unfold WellSorted.FreeTypeContext.map
        rw [lookup]
        simp only [Option.map_some]
        exact congrArg some
          (morphism.mapTypeExpr_costStatic_natural color sourceType)
    | @boundaryApplication sourceBound targetBound sourceAvailable thinning
        outer wireName arguments sourceType constructor rendered outsideCurrent
        certified certifies =>
        have mappedRendered :
            target.renderDeclaredCostConstructor
                (morphism.mapDeclaredCostConstructor constructor) =
              morphism.costWholeStructural.symbols.constructor wireName := by
          rw [morphism.render_mapDeclaredCostConstructor]
          exact congrArg
            morphism.costWholeStructural.symbols.constructor rendered
        have mappedOutside : target.declaredCostConstructorRole
              (morphism.mapDeclaredCostConstructor constructor) ≠
            .static color := by
          rw [morphism.declaredCostConstructorRole_map]
          exact outsideCurrent
        let mappedCertified := certified.mapStatic morphism scope
        have mappedContent :
            mapPattern morphism.costWholeStructural.symbols
                (.apply wireName arguments) =
              .apply
                (morphism.costWholeStructural.symbols.constructor wireName)
                (arguments.map
                  (mapPattern morphism.costWholeStructural.symbols)) := by
          simp [mapPattern, mapPatternList_eq_map]
        let mappedCertified' := mappedCertified.castContent mappedContent
        have mappedCertifies' :
            certifyCostRegionBoundary? target color
                (targetFree.map morphism.costWholeStructural.symbols)
                (targetAvailable.map
                  (mapTypeExpr morphism.costWholeStructural.symbols))
                (mapTypeExpr (color.symbols target)
                  (mapTypeExpr
                    morphism.underlying.structural.structural.symbols
                    sourceType))
                (.apply
                  (morphism.costWholeStructural.symbols.constructor wireName)
                  (arguments.map
                    (mapPattern morphism.costWholeStructural.symbols))) =
              some mappedCertified' := by
          simpa [mappedCertified', mappedCertified] using
            certified.certify_mapStatic_castContent_eq_some morphism scope
              certifies mappedContent
        let mappedBoundary : CostStaticRegionPlan target color
            (targetFree.map morphism.costWholeStructural.symbols)
            (sourceBound.map
              (mapTypeExpr
                morphism.underlying.structural.structural.symbols))
            (targetBound.map
              (mapTypeExpr morphism.costWholeStructural.symbols))
            (thinning.map morphism color)
            (targetAvailable.map
              (mapTypeExpr morphism.costWholeStructural.symbols))
            (CIGSLT.mapOneHoleContext
              morphism.costWholeStructural.symbols outer)
            (.apply
              (morphism.costWholeStructural.symbols.constructor wireName)
              (arguments.map
                (mapPattern morphism.costWholeStructural.symbols)))
            (mapTypeExpr
              morphism.underlying.structural.structural.symbols
              sourceType) :=
          CostStaticRegionPlan.boundaryApplication
            (morphism.mapDeclaredCostConstructor constructor) mappedRendered
            mappedOutside mappedCertified' mappedCertifies'
        exact CostStaticRegionPlan.reindex rfl rfl rfl rfl
          mappedContent.symm rfl mappedBoundary
    | @application sourceBound targetBound sourceAvailable thinning outer
        wireName arguments constructor rendered current preimage notBare
        children =>
        let mappedConstructor := morphism.mapDeclaredCostConstructor constructor
        let mappedPreimage := preimage.map morphism
        have mappedRendered : target.renderDeclaredCostConstructor
              mappedConstructor =
            morphism.costWholeStructural.symbols.constructor wireName := by
          dsimp [mappedConstructor]
          rw [morphism.render_mapDeclaredCostConstructor]
          exact congrArg morphism.costWholeStructural.symbols.constructor
            rendered
        have mappedCurrent : target.declaredCostConstructorRole
              mappedConstructor = .static color := by
          dsimp [mappedConstructor]
          rw [morphism.declaredCostConstructorRole_map]
          exact current
        have mappedNotBare : ¬ WellSorted.UsesBareCollection
            mappedPreimage.sourceConstructor.1 := by
          intro bare
          exact notBare
            ((WellSorted.usesBareCollection_mapGrammarRule_iff
              morphism.underlying.structural.structural.symbols
              preimage.sourceConstructor.1).mp bare)
        have argumentsObject :=
          WellSorted.objectArguments_of_objectApplication object
        have mappedChildren := mapCostStaticArgumentPlan morphism scope laws
          children argumentsObject
        have quoteEquality :
            ReflectiveContextSupport.isQuoteConstructor target.reflection.1
                mappedPreimage.sourceConstructor.1.label =
              ReflectiveContextSupport.isQuoteConstructor source.reflection.1
                preimage.sourceConstructor.1.label := by
          simpa [mappedPreimage, CostStaticConstructorPreimage.map,
            StructuralMorphism.mapConstructor, mapGrammarRule] using
            laws.quoteStatic_natural color
              preimage.sourceConstructor.1.label
        have availableEquality :
            (if ReflectiveContextSupport.isQuoteConstructor source.reflection.1
                preimage.sourceConstructor.1.label then [] else
              targetAvailable).map
                (mapTypeExpr morphism.costWholeStructural.symbols) =
              if ReflectiveContextSupport.isQuoteConstructor target.reflection.1
                  mappedPreimage.sourceConstructor.1.label then [] else
                targetAvailable.map
                  (mapTypeExpr morphism.costWholeStructural.symbols) := by
          rw [quoteEquality]
          split <;> rfl
        have parameterEquality :
            preimage.sourceConstructor.1.params.map
                (mapTermParam
                  morphism.underlying.structural.structural.symbols) =
              mappedPreimage.sourceConstructor.1.params := by
          rfl
        let mappedChildren' := CostStaticArgumentPlan.reindex
          (thinning₂ := thinning.map morphism color) rfl rfl
          availableEquality rfl rfl rfl rfl parameterEquality mappedChildren
        have mappedApplication :=
          CostStaticRegionPlan.application mappedConstructor mappedRendered
            mappedCurrent mappedPreimage mappedNotBare mappedChildren'
        have patternEquality :
            (.apply
              (morphism.costWholeStructural.symbols.constructor wireName)
              (arguments.map
                (mapPattern morphism.costWholeStructural.symbols))) =
              mapPattern morphism.costWholeStructural.symbols
                (.apply wireName arguments) := by
          simp [mapPattern, mapPatternList_eq_map]
        have typeEquality :
            (.base mappedPreimage.sourceConstructor.1.category : TypeExpr) =
              mapTypeExpr
                morphism.underlying.structural.structural.symbols
                (.base preimage.sourceConstructor.1.category) := by
          rfl
        exact CostStaticRegionPlan.reindex rfl rfl rfl rfl patternEquality
          typeEquality mappedApplication
    | @lambda sourceBound targetBound sourceAvailable thinning outer binder body
        domain codomain bodyPlan =>
        have bodyObject := WellSorted.objectBody_of_objectLambda object
        have mappedBody := mapCostStaticRegionPlan morphism scope laws bodyPlan
          bodyObject
        have targetTypeEquality :
            (mapTypeExpr morphism.costWholeStructural.symbols
                (mapTypeExpr (color.symbols source) domain) ::
              targetBound.map
                (mapTypeExpr morphism.costWholeStructural.symbols)) =
              (mapTypeExpr (color.symbols target)
                  (mapTypeExpr
                    morphism.underlying.structural.structural.symbols domain) ::
                targetBound.map
                  (mapTypeExpr morphism.costWholeStructural.symbols)) := by
          simp only [morphism.costWholeStructural_symbols]
          rw [morphism.mapTypeExpr_costStatic_natural]
        have availableEquality :
            (mapTypeExpr morphism.costWholeStructural.symbols
                (mapTypeExpr (color.symbols source) domain) ::
              targetAvailable.map
                (mapTypeExpr morphism.costWholeStructural.symbols)) =
              (mapTypeExpr (color.symbols target)
                  (mapTypeExpr
                    morphism.underlying.structural.structural.symbols domain) ::
                targetAvailable.map
                  (mapTypeExpr morphism.costWholeStructural.symbols)) := by
          simp only [morphism.costWholeStructural_symbols]
          rw [morphism.mapTypeExpr_costStatic_natural]
        have outerEquality :
            CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols
                (outer.comp (.lambda binder .hole)) =
              (CIGSLT.mapOneHoleContext
                  morphism.costWholeStructural.symbols outer).comp
                (.lambda binder .hole) := by
          simp [CIGSLT.mapOneHoleContext_contextComp,
            CIGSLT.mapOneHoleContext]
        let mappedBody' := CostStaticRegionPlan.reindex
          (thinning₂ := CostStaticBinderThinning.mapped
            (mapTypeExpr
              morphism.underlying.structural.structural.symbols domain)
            (thinning.map morphism color))
          rfl targetTypeEquality availableEquality outerEquality rfl rfl
          mappedBody
        simpa [mapPattern, mapTypeExpr] using
          CostStaticRegionPlan.lambda mappedBody'
    | @multiLambda sourceBound targetBound sourceAvailable thinning outer arity
        binders body domain codomain bodyPlan =>
        have bodyObject := WellSorted.objectBody_of_objectMultiLambda object
        have mappedBody := mapCostStaticRegionPlan morphism scope laws bodyPlan
          bodyObject
        have sourceBoundEquality :
            (List.replicate arity domain ++ sourceBound).map
                (mapTypeExpr
                  morphism.underlying.structural.structural.symbols) =
              List.replicate arity
                  (mapTypeExpr
                    morphism.underlying.structural.structural.symbols domain) ++
                sourceBound.map
                  (mapTypeExpr
                    morphism.underlying.structural.structural.symbols) := by
          simp [List.map_append, List.map_replicate]
        have targetBoundEquality :
            (List.replicate arity
                (mapTypeExpr (color.symbols source) domain) ++
              targetBound).map
                (mapTypeExpr morphism.costWholeStructural.symbols) =
              List.replicate arity
                  (mapTypeExpr (color.symbols target)
                    (mapTypeExpr
                      morphism.underlying.structural.structural.symbols
                      domain)) ++
                targetBound.map
                  (mapTypeExpr morphism.costWholeStructural.symbols) := by
          simp only [List.map_append, List.map_replicate,
            morphism.costWholeStructural_symbols]
          rw [morphism.mapTypeExpr_costStatic_natural]
        have availableEquality :
            (List.replicate arity
                (mapTypeExpr (color.symbols source) domain) ++
              targetAvailable).map
                (mapTypeExpr morphism.costWholeStructural.symbols) =
              List.replicate arity
                  (mapTypeExpr (color.symbols target)
                    (mapTypeExpr
                      morphism.underlying.structural.structural.symbols
                      domain)) ++
                targetAvailable.map
                  (mapTypeExpr morphism.costWholeStructural.symbols) := by
          simp only [List.map_append, List.map_replicate,
            morphism.costWholeStructural_symbols]
          rw [morphism.mapTypeExpr_costStatic_natural]
        have outerEquality :
            CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols
                (outer.comp (.multiLambda arity binders .hole)) =
              (CIGSLT.mapOneHoleContext
                  morphism.costWholeStructural.symbols outer).comp
                (.multiLambda arity binders .hole) := by
          simp [CIGSLT.mapOneHoleContext_contextComp,
            CIGSLT.mapOneHoleContext]
        let mappedBody' := CostStaticRegionPlan.reindex
          (thinning₂ := CostStaticBinderThinning.prependMapped arity
            (mapTypeExpr
              morphism.underlying.structural.structural.symbols domain)
            (thinning.map morphism color))
          sourceBoundEquality targetBoundEquality availableEquality
          outerEquality rfl rfl mappedBody
        simpa [mapPattern, mapTypeExpr] using
          CostStaticRegionPlan.multiLambda mappedBody'
    | @collection sourceBound targetBound sourceAvailable thinning outer
        collectionType elements rest sourceType choice selected children =>
        have elementsObject :=
          WellSorted.objectElements_of_objectCollection object
        let mappedChoice := choice.map
          morphism.underlying.structural.structural.symbols
        have mappedSelected :=
          morphism.maps_mem_costStaticCollectionTypingChoices color targetFree
            targetBound collectionType elements
            (mapTypeExpr (color.symbols source) sourceType) choice selected
            elementsObject
        simp only [morphism.costWholeStructural_symbols] at mappedSelected
        rw [morphism.mapTypeExpr_costStatic_natural] at mappedSelected
        have mappedChildren := mapCostStaticElementPlan
          (source := source) (target := target)
          (sourceBound := sourceBound) (targetBound := targetBound)
          (thinning := thinning) (sourceAvailable := targetAvailable)
          (outer := outer) (collectionType := collectionType)
          (before := []) (elements := elements) (rest := rest)
          (sourceElementType := choice.sourceElementType)
          morphism scope laws children elementsObject
        have mappedSelected' : mappedChoice ∈
            costStaticCollectionTypingChoices target color
              (targetFree.map morphism.costWholeStructural.symbols)
              (targetBound.map
                (mapTypeExpr morphism.costWholeStructural.symbols))
              collectionType
              (elements.map
                (mapPattern morphism.costWholeStructural.symbols))
              (mapTypeExpr (color.symbols target)
                (mapTypeExpr
                  morphism.underlying.structural.structural.symbols
                  sourceType)) := by
          simpa [mappedChoice, mapPatternList_eq_map] using mappedSelected
        have sourceElementTypeEquality :
            mapTypeExpr morphism.underlying.structural.structural.symbols
                choice.sourceElementType =
              mappedChoice.sourceElementType := by
          simp [mappedChoice,
            CostCollectionTypingChoice.sourceElementType_map]
        let mappedChildren' := CostStaticElementPlan.reindex
          (thinning₂ := thinning.map morphism color)
          rfl rfl rfl rfl rfl rfl rfl rfl sourceElementTypeEquality
          mappedChildren
        let mappedCollection : CostStaticRegionPlan target color
            (targetFree.map morphism.costWholeStructural.symbols)
            (sourceBound.map
              (mapTypeExpr
                morphism.underlying.structural.structural.symbols))
            (targetBound.map
              (mapTypeExpr morphism.costWholeStructural.symbols))
            (thinning.map morphism color)
            (targetAvailable.map
              (mapTypeExpr morphism.costWholeStructural.symbols))
            (CIGSLT.mapOneHoleContext
              morphism.costWholeStructural.symbols outer)
            (.collection collectionType
              (elements.map
                (mapPattern morphism.costWholeStructural.symbols)) rest)
            (mapTypeExpr
              morphism.underlying.structural.structural.symbols
              sourceType) :=
          CostStaticRegionPlan.collection mappedChoice mappedSelected'
            mappedChildren'
        have patternEquality :
            (.collection collectionType
                (elements.map
                  (mapPattern morphism.costWholeStructural.symbols)) rest) =
              mapPattern morphism.costWholeStructural.symbols
                (.collection collectionType elements rest) := by
          simp [mapPattern, mapPatternList_eq_map]
        exact CostStaticRegionPlan.reindex rfl rfl rfl rfl patternEquality
          rfl mappedCollection
    | @boundaryCollection sourceBound targetBound sourceAvailable thinning
        outer collectionType elements rest sourceType currentRejected
        oppositeChoice oppositeSelected certified certifies =>
        have elementsObject :=
          WellSorted.objectElements_of_objectCollection object
        let mappedOppositeChoice := oppositeChoice.map
          morphism.underlying.structural.structural.symbols
        have mappedRejected := laws.collectionRejectionPreserving color
          targetFree targetBound collectionType elements sourceType
          currentRejected
        have mappedSelected :=
          morphism.maps_mem_costStaticCollectionTypingChoices color.flip
            targetFree targetBound collectionType elements
            (mapTypeExpr (color.symbols source) sourceType) oppositeChoice
            oppositeSelected elementsObject
        simp only [morphism.costWholeStructural_symbols] at mappedSelected
        rw [morphism.mapTypeExpr_costStatic_natural color sourceType] at mappedSelected
        have mappedContent :
            mapPattern morphism.costWholeStructural.symbols
                (.collection collectionType elements rest) =
              .collection collectionType
                (elements.map
                  (mapPattern morphism.costWholeStructural.symbols)) rest := by
          simp [mapPattern, mapPatternList_eq_map]
        let mappedCertified :=
          (certified.mapStatic morphism scope).castContent mappedContent
        have mappedCertifies :=
          certified.certify_mapStatic_castContent_eq_some morphism scope
            certifies mappedContent
        let mappedBoundary : CostStaticRegionPlan target color
            (targetFree.map morphism.costWholeStructural.symbols)
            (sourceBound.map
              (mapTypeExpr
                morphism.underlying.structural.structural.symbols))
            (targetBound.map
              (mapTypeExpr morphism.costWholeStructural.symbols))
            (thinning.map morphism color)
            (targetAvailable.map
              (mapTypeExpr morphism.costWholeStructural.symbols))
            (CIGSLT.mapOneHoleContext
              morphism.costWholeStructural.symbols outer)
            (.collection collectionType
              (elements.map
                (mapPattern morphism.costWholeStructural.symbols)) rest)
            (mapTypeExpr
              morphism.underlying.structural.structural.symbols
              sourceType) :=
          CostStaticRegionPlan.boundaryCollection mappedRejected
            mappedOppositeChoice
            (by simpa [mapPatternList_eq_map] using mappedSelected)
            mappedCertified
            (by simpa [mappedCertified] using mappedCertifies)
        exact CostStaticRegionPlan.reindex rfl rfl rfl rfl
          mappedContent.symm rfl mappedBoundary
  termination_by 3 * sizeOf pattern + 2
  decreasing_by
    all_goals simp_all <;> omega

  def mapCostStaticArgumentPlan {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (objects : WellSorted.isObjectPatternList arguments = true) :
      CostStaticArgumentPlan target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (sourceBound.map
          (mapTypeExpr morphism.underlying.structural.structural.symbols))
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (thinning.map morphism color)
        (sourceAvailable.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols outer)
        (morphism.costWholeStructural.symbols.constructor wireName)
        (before.map (mapPattern morphism.costWholeStructural.symbols))
        (arguments.map (mapPattern morphism.costWholeStructural.symbols))
        (parameters.map
          (mapTermParam morphism.underlying.structural.structural.symbols)) := by
    cases plan with
    | @nil sourceBound targetBound sourceAvailable thinning outer wireName
        before =>
        exact CostStaticArgumentPlan.nil
    | @cons sourceBound targetBound sourceAvailable thinning outer wireName
        before argument arguments parameter parameters sourceExpected
        representation parameterType head tail =>
        have objectParts := WellSorted.objectList_cons objects
        apply CostStaticArgumentPlan.cons
        · exact (CIGSLT.matchesParameterRepresentation_mixed_map_iff
            morphism.underlying.structural.structural.symbols
            morphism.costWholeStructural.symbols parameter argument).2
              representation
        · simpa using congrArg
            (Option.map
              (mapTypeExpr
                morphism.underlying.structural.structural.symbols))
            parameterType
        · have mappedHead := mapCostStaticRegionPlan morphism scope laws head
            objectParts.1
          have outerEquality :
              CIGSLT.mapOneHoleContext
                  morphism.costWholeStructural.symbols
                  (outer.comp (.apply wireName before .hole arguments)) =
                (CIGSLT.mapOneHoleContext
                    morphism.costWholeStructural.symbols outer).comp
                  (.apply
                    (morphism.costWholeStructural.symbols.constructor wireName)
                    (before.map
                      (mapPattern morphism.costWholeStructural.symbols))
                    .hole
                    (arguments.map
                      (mapPattern morphism.costWholeStructural.symbols))) := by
            simp [CIGSLT.mapOneHoleContext_contextComp,
              CIGSLT.mapOneHoleContext]
          exact CostStaticRegionPlan.reindex rfl rfl rfl outerEquality
            rfl rfl mappedHead
        · have mappedTail := mapCostStaticArgumentPlan
            (source := source) (target := target)
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            (outer := outer) (wireName := wireName)
            (before := before ++ [argument]) (arguments := arguments)
            (parameters := parameters) morphism scope laws tail objectParts.2
          have beforeEquality :
              (before ++ [argument]).map
                  (mapPattern morphism.costWholeStructural.symbols) =
                before.map
                    (mapPattern morphism.costWholeStructural.symbols) ++
                  [mapPattern morphism.costWholeStructural.symbols argument] := by
            simp [List.map_append]
          exact CostStaticArgumentPlan.reindex
            (thinning₂ := thinning.map morphism color)
            rfl rfl rfl rfl rfl beforeEquality rfl rfl mappedTail
  termination_by 3 * sizeOf arguments + 1
  decreasing_by
    all_goals simp_all <;> omega

  def mapCostStaticElementPlan {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      (objects : WellSorted.isObjectPatternList elements = true) :
      CostStaticElementPlan target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (sourceBound.map
          (mapTypeExpr morphism.underlying.structural.structural.symbols))
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (thinning.map morphism color)
        (sourceAvailable.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols outer)
        collectionType
        (before.map (mapPattern morphism.costWholeStructural.symbols))
        (elements.map (mapPattern morphism.costWholeStructural.symbols)) rest
        (mapTypeExpr morphism.underlying.structural.structural.symbols
          sourceElementType) := by
    cases plan with
    | @nil sourceBound targetBound sourceAvailable thinning outer
        collectionType before rest sourceElementType =>
        exact CostStaticElementPlan.nil
    | @cons sourceBound targetBound sourceAvailable thinning outer
        collectionType before element elements rest sourceElementType head
        tail =>
        have objectParts := WellSorted.objectList_cons objects
        apply CostStaticElementPlan.cons
        · have mappedHead := mapCostStaticRegionPlan morphism scope laws head
            objectParts.1
          have outerEquality :
              CIGSLT.mapOneHoleContext
                  morphism.costWholeStructural.symbols
                  (outer.comp
                    (.collection collectionType before .hole elements rest)) =
                (CIGSLT.mapOneHoleContext
                    morphism.costWholeStructural.symbols outer).comp
                  (.collection collectionType
                    (before.map
                      (mapPattern morphism.costWholeStructural.symbols))
                    .hole
                    (elements.map
                      (mapPattern morphism.costWholeStructural.symbols)) rest) := by
            simp [CIGSLT.mapOneHoleContext_contextComp,
              CIGSLT.mapOneHoleContext]
          exact CostStaticRegionPlan.reindex rfl rfl rfl outerEquality
            rfl rfl mappedHead
        · have mappedTail := mapCostStaticElementPlan
            (source := source) (target := target)
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            (outer := outer) (collectionType := collectionType)
            (before := before ++ [element]) (elements := elements)
            (rest := rest) (sourceElementType := sourceElementType)
            morphism scope laws tail objectParts.2
          have beforeEquality :
              (before ++ [element]).map
                  (mapPattern morphism.costWholeStructural.symbols) =
                before.map
                    (mapPattern morphism.costWholeStructural.symbols) ++
                  [mapPattern morphism.costWholeStructural.symbols element] := by
            simp [List.map_append]
          exact CostStaticElementPlan.reindex
            (thinning₂ := thinning.map morphism color)
            rfl rfl rfl rfl rfl beforeEquality rfl rfl rfl mappedTail
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals simp_all <;> omega
end

private theorem argumentMeasure_lt_application (wireName : String)
    (arguments : List Pattern) :
    3 * sizeOf arguments + 1 <
      3 * sizeOf (Pattern.apply wireName arguments) + 2 := by
  simp
  omega

private theorem regionMeasure_lt_lambda (binder : Option String)
    (body : Pattern) :
    3 * sizeOf body + 2 < 3 * sizeOf (Pattern.lambda binder body) + 2 := by
  simp

private theorem regionMeasure_lt_multiLambda (arity : Nat)
    (binders : List String) (body : Pattern) :
    3 * sizeOf body + 2 <
      3 * sizeOf (Pattern.multiLambda arity binders body) + 2 := by
  simp

private theorem elementMeasure_lt_collection (collectionType : CollType)
    (elements : List Pattern) (rest : Option String) :
    3 * sizeOf elements + 1 <
      3 * sizeOf (Pattern.collection collectionType elements rest) + 2 := by
  simp
  omega

private theorem regionMeasure_lt_cons (head : Pattern)
    (tail : List Pattern) :
    3 * sizeOf head + 2 < 3 * sizeOf (head :: tail) + 1 := by
  simp
  omega

private theorem tailMeasure_lt_cons (head : Pattern)
    (tail : List Pattern) :
    3 * sizeOf tail + 1 < 3 * sizeOf (head :: tail) + 1 := by
  simp

mutual
  /-- Structural plan reindexing preserves every boundary occurrence and its
  chronological position. -/
  theorem mapCostStaticRegionPlan_occurrences {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {targetAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning targetAvailable outer pattern sourceType)
      (object : WellSorted.isObjectPattern pattern = true) :
      (mapCostStaticRegionPlan morphism scope laws plan object).occurrences =
        plan.occurrences.map (CostRegionOccurrence.map morphism) := by
    cases plan with
    | bvar | fvar =>
        rw [mapCostStaticRegionPlan.eq_1]
        rfl
    | boundaryApplication =>
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_occurrences]
        simp [CostStaticRegionPlan.occurrences, CostRegionOccurrence.map,
          mapPattern, mapPatternList_eq_map]
    | application constructor rendered current preimage notBare children =>
        have objects := WellSorted.objectArguments_of_objectApplication object
        have childEquality := mapCostStaticArgumentPlan_occurrences morphism
          scope laws children objects
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_occurrences]
        simp only [CostStaticRegionPlan.occurrences]
        apply Eq.trans ?_ childEquality
        apply CostStaticArgumentPlan.reindex_occurrences
    | lambda bodyPlan =>
        have bodyObject := WellSorted.objectBody_of_objectLambda object
        have bodyEquality := mapCostStaticRegionPlan_occurrences morphism scope
          laws bodyPlan bodyObject
        rw [mapCostStaticRegionPlan.eq_1]
        simpa [CostStaticRegionPlan.reindex_occurrences,
          CostStaticRegionPlan.occurrences] using bodyEquality
    | multiLambda bodyPlan =>
        have bodyObject := WellSorted.objectBody_of_objectMultiLambda object
        have bodyEquality := mapCostStaticRegionPlan_occurrences morphism scope
          laws bodyPlan bodyObject
        rw [mapCostStaticRegionPlan.eq_1]
        simpa [CostStaticRegionPlan.reindex_occurrences,
          CostStaticRegionPlan.occurrences] using bodyEquality
    | collection choice selected children =>
        have objects := WellSorted.objectElements_of_objectCollection object
        have childEquality := mapCostStaticElementPlan_occurrences morphism
          scope laws children objects
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_occurrences]
        simp only [CostStaticRegionPlan.occurrences]
        apply Eq.trans ?_ childEquality
        apply CostStaticElementPlan.reindex_occurrences
    | boundaryCollection =>
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_occurrences]
        simp [CostStaticRegionPlan.occurrences, CostRegionOccurrence.map,
          mapPattern, mapPatternList_eq_map]
  termination_by 3 * sizeOf pattern + 2
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Argument-spine reindexing maps and concatenates the exact occurrence
  sequence. -/
  theorem mapCostStaticArgumentPlan_occurrences {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (objects : WellSorted.isObjectPatternList arguments = true) :
      (mapCostStaticArgumentPlan morphism scope laws plan objects).occurrences =
        plan.occurrences.map (CostRegionOccurrence.map morphism) := by
    cases plan with
    | nil =>
        rw [mapCostStaticArgumentPlan.eq_1]
        rfl
    | cons representation parameterType head tail =>
        have objectParts := WellSorted.objectList_cons objects
        have headEquality := mapCostStaticRegionPlan_occurrences morphism scope
          laws head objectParts.1
        have tailEquality := mapCostStaticArgumentPlan_occurrences morphism
          scope laws tail objectParts.2
        rw [mapCostStaticArgumentPlan.eq_1]
        simp only [CostStaticArgumentPlan.occurrences]
        rw [CostStaticRegionPlan.reindex_occurrences,
          CostStaticArgumentPlan.reindex_occurrences]
        simpa [List.map_append] using
          congrArg₂ List.append headEquality tailEquality
  termination_by 3 * sizeOf arguments + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Collection-spine reindexing maps and concatenates the exact occurrence
  sequence. -/
  theorem mapCostStaticElementPlan_occurrences {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      (objects : WellSorted.isObjectPatternList elements = true) :
      (mapCostStaticElementPlan morphism scope laws plan objects).occurrences =
        plan.occurrences.map (CostRegionOccurrence.map morphism) := by
    cases plan with
    | nil =>
        rw [mapCostStaticElementPlan.eq_1]
        rfl
    | cons head tail =>
        have objectParts := WellSorted.objectList_cons objects
        have headEquality := mapCostStaticRegionPlan_occurrences morphism scope
          laws head objectParts.1
        have tailEquality := mapCostStaticElementPlan_occurrences morphism scope
          laws tail objectParts.2
        rw [mapCostStaticElementPlan.eq_1]
        simp only [CostStaticElementPlan.occurrences]
        rw [CostStaticRegionPlan.reindex_occurrences,
          CostStaticElementPlan.reindex_occurrences]
        simpa [List.map_append] using
          congrArg₂ List.append headEquality tailEquality
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

mutual
  /-- Structural plan mapping preserves the complete typed boundary table,
  not merely its occurrence index. -/
  theorem mapCostStaticRegionPlan_boundaryPacket {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {targetAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning targetAvailable outer pattern sourceType)
      (object : WellSorted.isObjectPattern pattern = true) :
      (mapCostStaticRegionPlan morphism scope laws plan object).boundaryPacket =
        TypedCostRegionBoundaryPacket.map morphism scope color
          plan.boundaryPacket := by
    have occurrenceNatural := mapCostStaticRegionPlan_occurrences morphism
      scope laws plan object
    cases plan with
    | bvar | fvar =>
        rw [mapCostStaticRegionPlan.eq_1]
        rfl
    | boundaryApplication =>
        have occurrenceNatural' := occurrenceNatural
        rw [mapCostStaticRegionPlan.eq_1,
          CostStaticRegionPlan.reindex_occurrences] at occurrenceNatural'
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_boundaryPacket]
        apply TypedCostRegionBoundaryPacket.ext_of_cast_eq occurrenceNatural'
        apply TypedCostRegionBoundaryTable.cast_singleton
        exact CertifiedCostRegionBoundary.castContent_mapStatic_typed
          morphism scope _ _
    | application constructor rendered current preimage notBare children =>
        have objects := WellSorted.objectArguments_of_objectApplication object
        have childNatural := mapCostStaticArgumentPlan_boundaryPacket morphism
          scope laws children objects
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_boundaryPacket]
        change (CostStaticArgumentPlan.reindex _ _ _ _ _ _ _ _
          (mapCostStaticArgumentPlan morphism scope laws children
            objects)).boundaryPacket = _
        rw [CostStaticArgumentPlan.reindex_boundaryPacket]
        exact childNatural
    | lambda bodyPlan =>
        have bodyObject := WellSorted.objectBody_of_objectLambda object
        have bodyNatural := mapCostStaticRegionPlan_boundaryPacket morphism scope
          laws bodyPlan bodyObject
        rw [mapCostStaticRegionPlan.eq_1]
        simp only
        change (CostStaticRegionPlan.reindex _ _ _ _ _ _
          (mapCostStaticRegionPlan morphism scope laws bodyPlan
            bodyObject)).boundaryPacket = _
        rw [CostStaticRegionPlan.reindex_boundaryPacket]
        exact bodyNatural
    | multiLambda bodyPlan =>
        have bodyObject := WellSorted.objectBody_of_objectMultiLambda object
        have bodyNatural := mapCostStaticRegionPlan_boundaryPacket morphism scope
          laws bodyPlan bodyObject
        rw [mapCostStaticRegionPlan.eq_1]
        simp only
        change (CostStaticRegionPlan.reindex _ _ _ _ _ _
          (mapCostStaticRegionPlan morphism scope laws bodyPlan
            bodyObject)).boundaryPacket = _
        rw [CostStaticRegionPlan.reindex_boundaryPacket]
        exact bodyNatural
    | collection choice selected children =>
        have objects := WellSorted.objectElements_of_objectCollection object
        have childNatural := mapCostStaticElementPlan_boundaryPacket morphism
          scope laws children objects
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_boundaryPacket]
        change (CostStaticElementPlan.reindex _ _ _ _ _ _ _ _ _
          (mapCostStaticElementPlan morphism scope laws children
            objects)).boundaryPacket = _
        rw [CostStaticElementPlan.reindex_boundaryPacket]
        exact childNatural
    | boundaryCollection =>
        have occurrenceNatural' := occurrenceNatural
        rw [mapCostStaticRegionPlan.eq_1,
          CostStaticRegionPlan.reindex_occurrences] at occurrenceNatural'
        rw [mapCostStaticRegionPlan.eq_1]
        rw [CostStaticRegionPlan.reindex_boundaryPacket]
        apply TypedCostRegionBoundaryPacket.ext_of_cast_eq occurrenceNatural'
        apply TypedCostRegionBoundaryTable.cast_singleton
        exact CertifiedCostRegionBoundary.castContent_mapStatic_typed
          morphism scope _ _
  termination_by 3 * sizeOf pattern + 2
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Argument-spine mapping retains every boundary certificate in order. -/
  theorem mapCostStaticArgumentPlan_boundaryPacket {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (objects : WellSorted.isObjectPatternList arguments = true) :
      (mapCostStaticArgumentPlan morphism scope laws plan
          objects).boundaryPacket =
        TypedCostRegionBoundaryPacket.map morphism scope color
          plan.boundaryPacket := by
    cases plan with
    | nil =>
        rw [mapCostStaticArgumentPlan.eq_1]
        rfl
    | cons representation parameterType head tail =>
        have objectParts := WellSorted.objectList_cons objects
        have headNatural := mapCostStaticRegionPlan_boundaryPacket morphism scope
          laws head objectParts.1
        have tailNatural := mapCostStaticArgumentPlan_boundaryPacket morphism
          scope laws tail objectParts.2
        have appended := congrArg₂ TypedCostRegionBoundaryPacket.append
          headNatural tailNatural
        have mappedAppend := TypedCostRegionBoundaryPacket.map_append
          morphism scope color head.boundaryPacket tail.boundaryPacket
        rw [mapCostStaticArgumentPlan.eq_1]
        change TypedCostRegionBoundaryPacket.append
            (CostStaticRegionPlan.reindex _ _ _ _ _ _
              (mapCostStaticRegionPlan morphism scope laws head
                objectParts.1)).boundaryPacket
            (CostStaticArgumentPlan.reindex _ _ _ _ _ _ _ _
              (mapCostStaticArgumentPlan morphism scope laws tail
                objectParts.2)).boundaryPacket = _
        rw [CostStaticRegionPlan.reindex_boundaryPacket,
          CostStaticArgumentPlan.reindex_boundaryPacket]
        exact appended.trans mappedAppend.symm
  termination_by 3 * sizeOf arguments + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Collection-spine mapping retains every boundary certificate in order. -/
  theorem mapCostStaticElementPlan_boundaryPacket {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      (objects : WellSorted.isObjectPatternList elements = true) :
      (mapCostStaticElementPlan morphism scope laws plan
          objects).boundaryPacket =
        TypedCostRegionBoundaryPacket.map morphism scope color
          plan.boundaryPacket := by
    cases plan with
    | nil =>
        rw [mapCostStaticElementPlan.eq_1]
        rfl
    | cons head tail =>
        have objectParts := WellSorted.objectList_cons objects
        have headNatural := mapCostStaticRegionPlan_boundaryPacket morphism scope
          laws head objectParts.1
        have tailNatural := mapCostStaticElementPlan_boundaryPacket morphism
          scope laws tail objectParts.2
        have appended := congrArg₂ TypedCostRegionBoundaryPacket.append
          headNatural tailNatural
        have mappedAppend := TypedCostRegionBoundaryPacket.map_append
          morphism scope color head.boundaryPacket tail.boundaryPacket
        rw [mapCostStaticElementPlan.eq_1]
        change TypedCostRegionBoundaryPacket.append
            (CostStaticRegionPlan.reindex _ _ _ _ _ _
              (mapCostStaticRegionPlan morphism scope laws head
                objectParts.1)).boundaryPacket
            (CostStaticElementPlan.reindex _ _ _ _ _ _ _ _ _
              (mapCostStaticElementPlan morphism scope laws tail
                objectParts.2)).boundaryPacket = _
        rw [CostStaticRegionPlan.reindex_boundaryPacket,
          CostStaticElementPlan.reindex_boundaryPacket]
        exact appended.trans mappedAppend.symm
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- Dependent index transport cannot change whether the retained plan starts
at a maximal static constructor. -/
theorem CostStaticRegionPlan.reindex_isStaticRoot
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {pattern₁ pattern₂ : Pattern}
    {sourceType₁ sourceType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (sourceType : sourceType₁ = sourceType₂)
    (plan : CostStaticRegionPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ pattern₁
        sourceType₁) :
    (plan.reindex (thinning₂ := thinning₂) sourceBound targetBound
        available outer pattern sourceType).isStaticRoot =
      plan.isStaticRoot := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst pattern₂
  subst sourceType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  rfl

/-- Structural plan mapping preserves maximal-static-root classification. -/
theorem mapCostStaticRegionPlan_isStaticRoot {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {targetAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning targetAvailable outer pattern sourceType)
    (object : WellSorted.isObjectPattern pattern = true) :
    (mapCostStaticRegionPlan morphism scope laws plan object).isStaticRoot =
      plan.isStaticRoot := by
  cases plan <;> rw [mapCostStaticRegionPlan.eq_1]
  all_goals first
    | rw [CostStaticRegionPlan.reindex_isStaticRoot]
    | rfl
  all_goals rfl

end Mettapedia.GSLT.LanguageDef
