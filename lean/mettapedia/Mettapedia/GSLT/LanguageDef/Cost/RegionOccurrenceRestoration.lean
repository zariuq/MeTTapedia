import Mettapedia.GSLT.LanguageDef.Cost.RegionPlanAbstraction

/-!
# Hygienic restoration of positional retained boundaries

The established source-variable namespace and exact occurrence tokens are
disjoint. Their combined context restores authored free variables literally
and reads each current retained value from its existing finite position.
This construction does not infer origins or require equal-key coherence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.OccurrenceRestoration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

private theorem sourceTag_ne_occurrenceTag (sourceName occurrenceName : String) :
    "$cost:region-source:" ++ sourceName ≠ "$cost:region-occurrence:" ++ occurrenceName := by
  intro equal
  have characters := congrArg String.toList equal
  simp [String.toList_append] at characters

/-- Even an arbitrary authored source name cannot collide with a local
occurrence token after the existing hygienic source tag is applied. -/
theorem sourceVariable_ne_token {size : Nat} (name : String) (slot : Fin size) :
    costRegionSourceVariableName name ≠ OccurrenceTokens.token slot :=
  sourceTag_ne_occurrenceTag name slot.val.repr

@[simp] theorem decodeSource_token {size : Nat} (slot : Fin size) :
    decodeCostRegionSourceVariableName (OccurrenceTokens.token slot) = none := by
  cases decoded : decodeCostRegionSourceVariableName (OccurrenceTokens.token slot) with
  | none => rfl
  | some name =>
      have equal := (decodeTaggedPayload_eq_some_iff costRegionSourceVariableTag
        (OccurrenceTokens.token slot) name).mp decoded
      exact False.elim (sourceVariable_ne_token name slot equal.symm)

@[simp] theorem lookup_sourceVariable (size : Nat) (name : String) :
    OccurrenceTokens.lookup size (costRegionSourceVariableName name) = none := by
  apply List.find?_eq_none.mpr
  intro slot _member
  simpa only [beq_iff_eq] using (sourceVariable_ne_token name slot).symm

variable {language : LanguageDef} {reflection : ReflectionProfile}
  {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
  {occurrences : List CostRegionOccurrence}

/-- Mapped skeleton variables use actual target sorts. A decoded authored
name reads the existing target free context; every other admitted name must
be an exact finite occurrence token. -/
def freeContext (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    WellSorted.FreeTypeContext :=
  fun name => match decodeCostRegionSourceVariableName name with
    | some original => targetFree original
    | none => OccurrenceTokens.freeContext table name

/-- Source variables are closed replacements; boundary tokens preserve their
own target binder support, including nonempty support. -/
def support (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    ContextSupport.Support :=
  fun name => match decodeCostRegionSourceVariableName name with
    | some _ => []
    | none => OccurrenceTokens.support table name

/-- Restore genuine source names and independent positional boundary values
through the same existing supported-substitution interface. -/
def assignment (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) :
    ContextSupport.Assignment :=
  fun name => match decodeCostRegionSourceVariableName name with
    | some original => .fvar original
    | none => OccurrenceTokens.assignment table values name

@[simp] theorem freeContext_sourceVariable
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) (name : String) :
    freeContext table (costRegionSourceVariableName name) = targetFree name := by
  simp only [freeContext, decodeCostRegionSourceVariableName_encode]

@[simp] theorem support_sourceVariable
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) (name : String) :
    support table (costRegionSourceVariableName name) = [] := by
  simp only [support, decodeCostRegionSourceVariableName_encode]

@[simp] theorem assignment_sourceVariable
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) (name : String) :
    assignment table values (costRegionSourceVariableName name) = .fvar name := by
  simp only [assignment, decodeCostRegionSourceVariableName_encode]

@[simp] theorem freeContext_token
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) (slot : Slot table) :
    freeContext table (OccurrenceTokens.token slot) = some (table.entries.get slot).boundary.targetType := by
  simp only [freeContext, decodeSource_token, OccurrenceTokens.freeContext_token]

@[simp] theorem support_token
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) (slot : Slot table) :
    support table (OccurrenceTokens.token slot) = (table.entries.get slot).boundary.targetSupport := by
  simp only [support, decodeSource_token, OccurrenceTokens.support_token]

@[simp] theorem assignment_token
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) (slot : Slot table) :
    assignment table values (OccurrenceTokens.token slot) = (get table values slot).1 := by
  simp only [assignment, decodeSource_token, OccurrenceTokens.assignment_token]

/-- The combined restoration assignment is constructed from target-context
lookup and the existing vector's typing/scope certificates. -/
def supportedAssignment
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) :
    WellSorted.SupportedOpenAssignment reflection language (freeContext table) targetFree (support table) where
  assignment := assignment table values
  typed := by
    intro name type typed
    cases decoded : decodeCostRegionSourceVariableName name with
    | none =>
        have prior := (OccurrenceTokens.supportedAssignment table values).typed
          (by simpa only [freeContext, decoded] using typed)
        simpa only [assignment, support, decoded, OccurrenceTokens.supportedAssignment] using prior
    | some original =>
        have lookup : targetFree original = some type := by
          simpa only [freeContext, decoded] using typed
        simpa only [assignment, support, decoded] using
          (WellSorted.HasType.fvar (bound := []) lookup)
  canonicalBinderMetadata := by
    intro name type typed
    cases decoded : decodeCostRegionSourceVariableName name with
    | none =>
        have prior := (OccurrenceTokens.supportedAssignment table values).canonicalBinderMetadata
          (by simpa only [freeContext, decoded] using typed)
        simpa only [assignment, decoded, OccurrenceTokens.supportedAssignment] using prior
    | some original => simp [assignment, decoded, Pattern.hasCanonicalBinderMetadata]
  objectPattern := by
    intro name type typed
    cases decoded : decodeCostRegionSourceVariableName name with
    | none =>
        have prior := (OccurrenceTokens.supportedAssignment table values).objectPattern
          (by simpa only [freeContext, decoded] using typed)
        simpa only [assignment, decoded, OccurrenceTokens.supportedAssignment] using prior
    | some original => simp [assignment, decoded, WellSorted.isObjectPattern]
  reflectiveScopeSafe := by
    intro name type typed
    cases decoded : decodeCostRegionSourceVariableName name with
    | none =>
        have prior := (OccurrenceTokens.supportedAssignment table values).reflectiveScopeSafe
          (by simpa only [freeContext, decoded] using typed)
        simpa only [assignment, support, decoded, OccurrenceTokens.supportedAssignment] using prior
    | some original =>
        intro declaration _member
        simp [assignment, decoded, binderSafeAt]

/-- Source-name restoration does not erase positional distinctions. -/
theorem assignment_injective
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    Function.Injective (assignment table) := by
  intro first second equal
  apply ext_get
  intro slot
  apply Subtype.ext
  have value := congrFun equal (OccurrenceTokens.token slot)
  simpa only [assignment_token] using value

end Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.OccurrenceRestoration
