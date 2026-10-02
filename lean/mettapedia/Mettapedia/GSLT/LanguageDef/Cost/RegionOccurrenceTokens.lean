import Mettapedia.GSLT.LanguageDef.Cost.RegionBoundaryOccurrenceMap
import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.OSLF.MeTTaIL.DecimalNames
import Mathlib.Data.List.FinRange

/-!
# Supported substitution for retained occurrence tokens

Tokens encode existing finite table positions, independently of immutable
boundary keys. Exact finite lookup recovers the position, so independent
current values give a genuine supported open assignment. This boundary-only
free context does not replace the region planner or infer source-variable
support; integration with the complete source skeleton remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.OccurrenceTokens
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open TypedCostRegionBoundaryTable.Values

/-- A local token names one existing position in its enclosing table. -/
def token {size : Nat} (slot : Fin size) : String := "$cost:region-occurrence:" ++ slot.val.repr

theorem token_injective {size : Nat} : Function.Injective (token (size := size)) := by
  intro first second equal
  apply Fin.ext
  apply Mettapedia.OSLF.MeTTaIL.DecimalNames.repr_injective
  exact (String.append_right_inj "$cost:region-occurrence:").mp equal

/-- Lookup verifies the exact token against the complete finite enumeration. -/
def lookup (size : Nat) (name : String) : Option (Fin size) :=
  (List.finRange size).find? (fun slot => token slot == name)

@[simp] theorem lookup_token {size : Nat} (slot : Fin size) : lookup size (token slot) = some slot := by
  cases found : lookup size (token slot) with
  | none =>
      have absent := List.find?_eq_none.mp found
      have impossible := absent slot (List.mem_finRange slot)
      simp at impossible
  | some selected =>
      have same : token selected = token slot := by
        simpa only [beq_iff_eq] using List.find?_some found
      have equal := token_injective same
      subst selected
      rfl

variable {language : LanguageDef} {reflection : ReflectionProfile}
  {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
  {occurrences : List CostRegionOccurrence}

/-- Result types are read from the exact selected occurrence. -/
def freeContext (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    WellSorted.FreeTypeContext :=
  fun name => (lookup table.entries.length name).map (fun slot => (table.entries.get slot).boundary.targetType)

/-- Each token retains its own target binder support. -/
def support (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    ContextSupport.Support :=
  fun name => match lookup table.entries.length name with
    | some slot => (table.entries.get slot).boundary.targetSupport
    | none => []

@[simp] theorem freeContext_token
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (slot : Slot table) : freeContext table (token slot) =
      some (table.entries.get slot).boundary.targetType := by
  simp only [freeContext, lookup_token, Option.map_some]

@[simp] theorem support_token
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (slot : Slot table) : support table (token slot) =
      (table.entries.get slot).boundary.targetSupport := by
  simp only [support, lookup_token]

/-- Positional assignment reads every current occurrence independently. -/
def assignment (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) :
    ContextSupport.Assignment :=
  fun name => match lookup table.entries.length name with
    | some slot => (get table values slot).1
    | none => .fvar name

@[simp] theorem assignment_token
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table)
    (slot : Slot table) : assignment table values (token slot) = (get table values slot).1 := by
  simp only [assignment, lookup_token]

/-- The existing supported-open assignment is constructed from the vector's certificates. -/
def supportedAssignment
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) :
    WellSorted.SupportedOpenAssignment reflection language (freeContext table) targetFree (support table) where
  assignment := assignment table values
  typed := by
    intro name type typed
    cases found : lookup table.entries.length name with
    | none => simp [freeContext, found] at typed
    | some slot =>
        have expected : (table.entries.get slot).boundary.targetType = type := by
          simpa only [freeContext, found, Option.map_some, Option.some.injEq] using typed
        subst type
        simpa only [assignment, support, found] using (get table values slot).2.1.1
  canonicalBinderMetadata := by
    intro name type typed
    cases found : lookup table.entries.length name with
    | none => simp [freeContext, found] at typed
    | some slot => simpa only [assignment, found] using (get table values slot).2.1.2.1
  objectPattern := by
    intro name type typed
    cases found : lookup table.entries.length name with
    | none => simp [freeContext, found] at typed
    | some slot => simpa only [assignment, found] using (get table values slot).2.1.2.2.1
  reflectiveScopeSafe := by
    intro name type typed
    cases found : lookup table.entries.length name with
    | none => simp [freeContext, found] at typed
    | some slot => simpa only [assignment, support, found] using (get table values slot).2.2

/-- Exact token assignment retains the entire current vector, including equal-key entries. -/
theorem assignment_injective
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    Function.Injective (assignment table) := by
  intro first second equal
  apply ext_get
  intro slot
  apply Subtype.ext
  have read := congrFun equal (token slot)
  simpa only [assignment_token] using read

/-- An explicit origin map is respected by token readout, including copied origins. -/
theorem assignment_pullback {sourceOccurrences targetOccurrences : List CostRegionOccurrence}
    (source : TypedCostRegionBoundaryTable language reflection color targetFree sourceOccurrences)
    (target : TypedCostRegionBoundaryTable language reflection color targetFree targetOccurrences)
    (origin : Slot target → Slot source)
    (boundary : ∀ slot, (target.entries.get slot).boundary =
      (source.entries.get (origin slot)).boundary)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree source)
    (slot : Slot target) :
    assignment target (pullback source target origin boundary values) (token slot) =
      assignment source values (token (origin slot)) := by
  simp only [assignment_token, get_pullback_pattern]

end Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.OccurrenceTokens
