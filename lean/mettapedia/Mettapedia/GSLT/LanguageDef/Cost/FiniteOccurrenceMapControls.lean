import Mathlib.Tactic.FinCases
import Mettapedia.GSLT.LanguageDef.Cost.RegionOccurrenceTokens
import Mettapedia.GSLT.LanguageDef.Cost.FiniteRegionBoundaryControls

/-!
# Copied, permuted and omitted synchronous boundary origins

These maps use the actual admitted synchronous values and existing finite
positions. Equal immutable keys do not prevent a permutation from observing
independent values. Copying one selected origin initializes two equal values;
a later positional update can separate them again.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.FiniteOccurrenceMapControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open FiniteRegionBoundaryControls
open Synchronous
open CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values

private theorem same_boundary (first second : Slot table) :
    (table.entries.get first).boundary = (table.entries.get second).boundary := by
  change Fin 2 at first second
  fin_cases first <;> fin_cases second <;> rfl

def permuted := pullback table table Fin.rev (fun slot => same_boundary slot slot.rev) values

def copied := pullback table table (fun _ => first) (fun slot => same_boundary slot first) values

/-- The two equal-key positions have exchanged their distinct actual current values. -/
theorem permutation_readout :
    (get table permuted first).1 = output ∧ (get table permuted second).1 = zero := by
  constructor <;> rfl

/-- Copying selects a particular origin, not the first matching immutable key. -/
theorem copy_readout :
    (get table copied first).1 = zero ∧ (get table copied second).1 = zero := by
  constructor <;> rfl

/-- Copies remain independently writable at their retained positions. -/
theorem updated_copy_readout :
    (get table (set table copied second outputValue) first).1 = zero ∧
      (get table (set table copied second outputValue) second).1 = output := by
  constructor <;> rfl

def singletonTable : TypedCostRegionBoundaryTable communicationDecoration FiniteWhole.sourceReflection
    .wrapped (fun _ => none) [firstOccurrence] := .cons boundary rfl .nil

def omitted := pullback table singletonTable (fun _ => second)
  (fun slot => by
    change Fin 1 at slot
    fin_cases slot
    rfl) values

/-- Omitting the first origin retains the chosen second value. -/
theorem omission_readout : (get singletonTable omitted ⟨0, by decide⟩).1 = output := rfl

/-- Same keys cannot justify forgetting the origin permutation. -/
theorem permutation_changes_values : permuted ≠ values := by
  intro equal
  have firstEqual := congrArg (fun current => (get table current first).1) equal
  have different : output ≠ zero := by decide +kernel
  exact different firstEqual

namespace TokenRestoration
open CostRegionBoundaryEvidence.OccurrenceTokens
open WellSorted

def skeleton : Pattern := .collection .hashBag [.fvar (token first), .fvar (token second)] none

def parallelRule : GrammarRule :=
  costWrappedConstructor (theory := rhoSyncIGSLT) rhoParallelConstructor.1

private theorem parallelRule_mem : parallelRule ∈ communicationDecoration.costWholeLanguage.terms := by
  decide +kernel

theorem skeleton_typed : HasType communicationDecoration.costWholeLanguage
    (freeContext table) [] skeleton (.base costWrappedSortName) :=
  .collectionConstructor (rule := parallelRule) parallelRule_mem rfl
    (.cons (.fvar (freeContext_token table first))
      (.cons (.fvar (freeContext_token table second)) (.nil [] (.base costWrappedSortName))))

theorem skeleton_safe : skeleton_typed.ReflectiveSupportSafeAt
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    (support table) [] := by
  exact HasType.ReflectiveSupportSafeAt.collectionConstructor
    (profile := communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    (support := support table) (membership := parallelRule_mem) (parameterShape := rfl) (.cons
    (.fvar (freeContext_token table first) [] ⟨[], rfl⟩)
    (.cons (.fvar (freeContext_token table second) [] ⟨[], rfl⟩)
      (.nil [] (.base costWrappedSortName) [])))

def openSkeleton : ReflectiveWellSorted.OpenPattern
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    communicationDecoration.costWholeLanguage (freeContext table) [] (.base costWrappedSortName) :=
  ⟨skeleton, ⟨skeleton_typed, rfl, rfl, skeleton_typed.isWellScopedAt⟩, by intro declaration member; rfl⟩

/-- Use the existing typed, quote-aware substitution engine with positional tokens. -/
def restored := ReflectiveWellSorted.OpenPattern.substituteReflectiveSupported
  openSkeleton (supportedAssignment table values) skeleton_safe

/-- Both equal-key positions are restored with their independent current values. -/
theorem restored_exact : restored.1 = .collection .hashBag [zero, output] none := by
  change ReflectiveContextSupport.substitute
    (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
    (support table) (assignment table values) [] skeleton = _
  simp only [ReflectiveContextSupport.substitute, skeleton,
    ReflectiveContextSupport.substituteAt, List.map_cons, List.map_nil,
    assignment_token, support_token]
  rfl

theorem tokens_distinguish_permutation : assignment table permuted ≠ assignment table values := by
  intro equal
  exact permutation_changes_values (assignment_injective table equal)

end TokenRestoration
end Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.FiniteOccurrenceMapControls
