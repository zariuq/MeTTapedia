import Mettapedia.GSLT.LanguageDef.Cost.FiniteRegionBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteWhole

/-!
# Independent current values at repeated synchronous boundary keys

Two retained positions share the same complete immutable boundary record.
Their current values are independently admitted in the actual synchronous
finite grammar; replacing the first position leaves the second unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.FiniteRegionBoundaryControls
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Synchronous WellSorted ReflectionExtension

def zero : Pattern := .apply (costWrappedConstructorName "PZero") []

def output : Pattern := .apply costSignedConstructorName
  [.apply (costBaseConstructorName "POutputK")
    [.apply (costWrappedConstructorName "NQuote") [zero], zero, zero],
   .apply costSignatureUnitConstructorName []]

private theorem zero_sealed : ReflectiveWellSorted.ReflectiveScopeSafeAt
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1) 0 zero := by
  intro declaration member
  simp only [FiniteWhole.sourceReflection, costWholeReflectionProfile,
    costStaticReflectivePresentations, rhoReflectionProfile, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

private theorem output_sealed : ReflectiveWellSorted.ReflectiveScopeSafeAt
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1) 0 output := by
  intro declaration member
  simp only [FiniteWhole.sourceReflection, costWholeReflectionProfile,
    costStaticReflectivePresentations, rhoReflectionProfile, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

def zeroValue : ReflectiveWellSorted.OpenPattern
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    communicationDecoration.costWholeLanguage (fun _ => none) [] (.base costWrappedSortName) :=
  ⟨zero, ⟨checkHasType_sound (by decide +kernel), by decide +kernel,
    by decide +kernel, by change zero.isWellScopedAt 0 = true; decide +kernel⟩, zero_sealed⟩

def outputValue : ReflectiveWellSorted.OpenPattern
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    communicationDecoration.costWholeLanguage (fun _ => none) [] (.base costWrappedSortName) :=
  ⟨output, ⟨checkHasType_sound (by decide +kernel), by decide +kernel,
    by decide +kernel, by change output.isWellScopedAt 0 = true; decide +kernel⟩, output_sealed⟩

def boundary : TypedCostRegionBoundary communicationDecoration FiniteWhole.sourceReflection
    .wrapped (fun _ => none) where
  boundary := ⟨.base "Proc", [], .base costWrappedSortName, [], zero⟩
  contentTyped := zeroValue.2.1.1
  contentCanonicalBinderMetadata := zeroValue.2.1.2.1
  contentObjectPattern := zeroValue.2.1.2.2.1
  contentReflectiveScopeSafe := zeroValue.2.2

def firstOccurrence : CostRegionOccurrence :=
  ⟨.collection .hashBag [] .hole [zero] none, zero⟩
def secondOccurrence : CostRegionOccurrence :=
  ⟨.collection .hashBag [zero] .hole [] none, zero⟩

theorem occurrence_reconstruction :
    firstOccurrence.context.fill firstOccurrence.content = .collection .hashBag [zero, zero] none ∧
    secondOccurrence.context.fill secondOccurrence.content = .collection .hashBag [zero, zero] none := by
  constructor <;> rfl

def table : TypedCostRegionBoundaryTable communicationDecoration FiniteWhole.sourceReflection
    .wrapped (fun _ => none) [firstOccurrence, secondOccurrence] :=
  .cons boundary rfl (.cons boundary rfl .nil)

def values : TypedCostRegionBoundaryTable.Values communicationDecoration FiniteWhole.sourceReflection
    .wrapped (fun _ => none) table := .cons zeroValue (.cons outputValue .nil)

def first : TypedCostRegionBoundaryTable.Values.Slot table := ⟨0, by decide +kernel⟩
def second : TypedCostRegionBoundaryTable.Values.Slot table := ⟨1, by decide +kernel⟩

/-- All five key coordinates agree, while the actual finite target values differ. -/
theorem equal_keys_independent_values :
    (table.entries.get first).boundary = (table.entries.get second).boundary ∧
      (TypedCostRegionBoundaryTable.Values.get table values first).1 ≠
        (TypedCostRegionBoundaryTable.Values.get table values second).1 := by
  constructor
  · rfl
  · decide +kernel

/-- A positional update affects precisely the chosen occurrence. -/
theorem first_update_preserves_second :
    TypedCostRegionBoundaryTable.Values.get table
      (TypedCostRegionBoundaryTable.Values.set table values first outputValue) second = outputValue := by
  rw [TypedCostRegionBoundaryTable.Values.get_set_other table values first second outputValue
    (by decide +kernel)]
  rfl

/-- Whole-key lookup cannot represent these two independently updated positions. -/
theorem no_boundary_function_for_both :
    ¬∃ readout : CostRegionBoundary → Pattern,
      readout (table.entries.get first).boundary =
        (TypedCostRegionBoundaryTable.Values.get table values first).1 ∧
      readout (table.entries.get second).boundary =
        (TypedCostRegionBoundaryTable.Values.get table values second).1 := by
  rintro ⟨readout, firstRead, secondRead⟩
  apply equal_keys_independent_values.2
  exact firstRead.symm.trans ((congrArg readout equal_keys_independent_values.1).trans secondRead)

end Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.FiniteRegionBoundaryControls
