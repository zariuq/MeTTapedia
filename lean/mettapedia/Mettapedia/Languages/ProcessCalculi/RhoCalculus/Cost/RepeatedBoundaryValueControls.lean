import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RetainedBoundaryGraftControls
import Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues

/-!
# Independent current values at repeated rho boundaries

An actual static rho parallel frame has two occurrences of the same input.
Its immutable content lookup and original restoration are correct.  The two
aligned current-value vectors below differ at the second occurrence, but
the name-based current lookup selects the first occurrence in both vectors.
Consequently compact restoration forgets their independent second update,
while the full retained semantic child forests still distinguish it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryValueControls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted
open LanguageDefContinuedInteraction CostCanonicalLaws
open RetainedBoundaryGraftControls
open RetainedBoundaryOriginTransport

def parallelRule : GrammarRule :=
  { label := "PPar", category := "Proc"
    params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)]
    syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"]
    algebra? := some { flatten := true, unit := some "PZero" } }

def originalPattern : Pattern := .collection .hashBag [inputPattern, inputPattern] none

def choice : CostCollectionTypingChoice := .bare parallelRule (.base "Proc")

theorem selected : choice ∈ costStaticCollectionTypingChoices rhoCIGSLT .base
    FreeTypeContext.empty [] .hashBag [inputPattern, inputPattern]
    (.base (costBaseSortName "Proc")) := by decide +kernel

def plan : CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
    (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
    (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base []) []
    .hole originalPattern (.base "Proc") :=
  .collection choice selected
    (.cons (StaticLeafBoundaryRefinement.replacementPlan
      (thinning := CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      inputPrincipal input_not_static inputArguments input_admitted
      (.collection .hashBag [] .hole [inputPattern] none))
      (.cons (StaticLeafBoundaryRefinement.replacementPlan
        (thinning := CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
        inputPrincipal input_not_static inputArguments input_admitted
        (.collection .hashBag [inputPattern] .hole [] none)) .nil))

theorem original_admitted : ReflectiveWellSorted.OpenPatternWellSorted
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [] (.base (costBaseSortName "Proc")) originalPattern :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _ _).mp
    (by decide +kernel)

def frame : CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan
    (sourceSort := ⟨"Proc", by decide +kernel⟩)
    ⟨originalPattern, original_admitted.1⟩ plan rfl

theorem distinct_occurrences : plan.occurrences.length = 2 ∧
    plan.occurrences[0]? ≠ plan.occurrences[1]? := by
  constructor
  · rfl
  · decide +kernel

theorem repeated_entries : frame.boundaryTable.entries =
    [(StaticLeafBoundaryRefinement.boundary input_admitted).typed,
     (StaticLeafBoundaryRefinement.boundary input_admitted).typed] := rfl

def inputValue : ReflectiveWellSorted.OpenPattern rhoCIGSLT.costWholeReflectionProfile
    rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] (.base (costBaseSortName "Proc")) :=
  ⟨inputPattern, input_admitted⟩

def zeroPattern : Pattern := .apply (costBaseConstructorName "PZero") []

theorem zero_admitted : ReflectiveWellSorted.OpenPatternWellSorted
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [] (.base (costBaseSortName "Proc")) zeroPattern :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _ _).mp
    (by decide +kernel)

def zeroValue : ReflectiveWellSorted.OpenPattern rhoCIGSLT.costWholeReflectionProfile
    rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] (.base (costBaseSortName "Proc")) :=
  ⟨zeroPattern, zero_admitted⟩

def uniformValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
    FreeTypeContext.empty frame.boundaryTable := .cons inputValue (.cons inputValue .nil)

def mixedValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
    FreeTypeContext.empty frame.boundaryTable := .cons inputValue (.cons zeroValue .nil)

def secondSlot : BoundaryOccurrenceValues.Slot frame.boundaryTable := ⟨1, by decide +kernel⟩

def firstSlot : BoundaryOccurrenceValues.Slot frame.boundaryTable := ⟨0, by decide +kernel⟩

theorem slots_different : firstSlot ≠ secondSlot := by decide +kernel

/-- Positional lookup observes the independently changed second value. -/
theorem positional_second_values :
    (BoundaryOccurrenceValues.get frame.boundaryTable mixedValues secondSlot).1 = zeroPattern ∧
    (BoundaryOccurrenceValues.get frame.boundaryTable uniformValues secondSlot).1 = inputPattern := by
  constructor <;> rfl

theorem current_values_different : mixedValues ≠ uniformValues := by
  intro equal
  have secondEqual := congrArg
    (fun values => (BoundaryOccurrenceValues.get frame.boundaryTable values secondSlot).1) equal
  have different : zeroPattern ≠ inputPattern := by decide +kernel
  exact different secondEqual

/-- Updating only the second retained occurrence constructs the mixed
vector, despite both positions having the same immutable key. -/
theorem positional_second_update :
    BoundaryOccurrenceValues.set frame.boundaryTable uniformValues secondSlot zeroValue =
      mixedValues := rfl

theorem independent_updates_commute :
    BoundaryOccurrenceValues.set frame.boundaryTable
      (BoundaryOccurrenceValues.set frame.boundaryTable uniformValues firstSlot zeroValue)
      secondSlot zeroValue =
    BoundaryOccurrenceValues.set frame.boundaryTable
      (BoundaryOccurrenceValues.set frame.boundaryTable uniformValues secondSlot zeroValue)
      firstSlot zeroValue :=
  BoundaryOccurrenceValues.set_commute frame.boundaryTable uniformValues firstSlot
    secondSlot zeroValue zeroValue slots_different

/-- The original immutable table restores the certified source accurately. -/
theorem original_restoration : frame.boundaryTable.restoreSupportedSkeleton []
    frame.mappedThickenedSkeleton.1 = originalPattern :=
  frame.restore_mappedThickenedSkeleton_eq_term

/-- Changing the second current value does not change any name-based lookup. -/
theorem resolve_same (name : String) :
    mixedValues.resolve frame.boundaryTable name =
      uniformValues.resolve frame.boundaryTable name := by
  let b := (StaticLeafBoundaryRefinement.boundary input_admitted).typed
  let key := costRegionBoundaryVariableName b.boundary
  let first : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT .base
      FreeTypeContext.empty := ⟨b, inputValue⟩
  let second : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT .base
      FreeTypeContext.empty := ⟨b, zeroValue⟩
  change (if name = key then some first
      else if name = key then some second else none) =
    (if name = key then some first
      else if name = key then some first else none)
  by_cases matched : name = key <;> simp [matched]

theorem assignment_same : mixedValues.assignment frame.boundaryTable =
    uniformValues.assignment frame.boundaryTable := by
  funext name
  simp only [TypedCostRegionBoundaryTable.Values.assignment, resolve_same]

/-- Compact restoration is insensitive to this independent second update. -/
theorem restoration_same (bound : List TypeExpr) (skeleton : Pattern) :
    mixedValues.restoreSupportedSkeleton frame.boundaryTable bound skeleton =
      uniformValues.restoreSupportedSkeleton frame.boundaryTable bound skeleton := by
  simp only [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton, assignment_same]

def zeroTree : CostSemanticTree rhoCIGSLT FreeTypeContext.empty [] []
    zeroPattern (.base (costBaseSortName "Proc")) :=
  CostSemanticOpenElaboration.compile rhoCIGSLT rho_costStaticCanonicalPathSafe
    (targetSort := CostStaticColor.base.mapLangSort rhoCIGSLT
      rhoCIGSLT.theory.presentation.interactingLangSort)
    ⟨zeroPattern, zero_admitted⟩

def uniformChildren : CostSemanticBoundaryTrees rhoCIGSLT FreeTypeContext.empty
    .base frame.boundaryTable uniformValues := .cons inputTree (.cons inputTree .nil)

def mixedChildren : CostSemanticBoundaryTrees rhoCIGSLT FreeTypeContext.empty
    .base frame.boundaryTable mixedValues := .cons inputTree (.cons zeroTree .nil)

theorem positional_second_tree_update :
    BoundaryOccurrenceValues.setTree frame.boundaryTable uniformValues uniformChildren
      secondSlot zeroValue zeroTree = mixedChildren := rfl

/-- Complete ordered descendants retain the independent second update. -/
theorem retained_children_different :
    packedChildren mixedChildren ≠ packedChildren uniformChildren := by
  intro equal
  have tailEqual := (List.cons.inj equal).2
  have secondEqual := (List.cons.inj tailEqual).1
  have patternsEqual := congrArg (fun child : PackedTree rhoCIGSLT FreeTypeContext.empty =>
    child.2.1) secondEqual
  have different : zeroPattern ≠ inputPattern := by decide +kernel
  exact different patternsEqual

#print axioms distinct_occurrences
#print axioms repeated_entries
#print axioms original_restoration
#print axioms positional_second_values
#print axioms current_values_different
#print axioms positional_second_update
#print axioms independent_updates_commute
#print axioms positional_second_tree_update
#print axioms resolve_same
#print axioms restoration_same
#print axioms retained_children_different

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryValueControls
