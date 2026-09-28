import Mettapedia.GSLT.LanguageDef.TypedSideOccurrenceAdmission
import Mettapedia.GSLT.LanguageDef.RestAwareChecker

/-!
# Sorted occurrence arguments from authored declarations

Structural binding admission verifies that row arguments are locally scoped.
It does not verify their declared sorts. The checker here compares the actual
ordered row list with its dependency sorts in the binder context extracted
from the authored occurrence address. Its soundness is relative to the
rest-aware schema checker; no completeness of that checker is asserted.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- Check every supplied argument against the corresponding declared
dependency sort. The recursive shape checks exact arity without truncation. -/
def checkOccurrenceArguments (language : LanguageDef)
    (free : FreeTypeContext) (locals ambient : List TypeExpr) :
    List Pattern → List TypeExpr → Bool
  | [], [] => true
  | argument :: arguments, dependency :: dependencies =>
      checkSchemaHasType language free (locals ++ ambient)
        argument dependency &&
      checkOccurrenceArguments language free locals ambient
        arguments dependencies
  | _, _ => false

/-- Successful ordered checking yields precisely the `Forall₂` premise
consumed by the typed executable substitution law. -/
theorem checkOccurrenceArguments_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {locals ambient : List TypeExpr}
    {arguments : List Pattern} {dependencies : List TypeExpr}
    (checked : checkOccurrenceArguments language free locals ambient
      arguments dependencies = true) :
    List.Forall₂
      (fun argument dependency =>
        HasType language free (locals ++ ambient) argument dependency)
      arguments dependencies := by
  induction arguments generalizing dependencies with
  | nil =>
      cases dependencies with
      | nil => exact .nil
      | cons _ _ => simp [checkOccurrenceArguments] at checked
  | cons argument arguments inductionHypothesis =>
      cases dependencies with
      | nil => simp [checkOccurrenceArguments] at checked
      | cons dependency dependencies =>
          simp only [checkOccurrenceArguments, Bool.and_eq_true] at checked
          exact .cons (checkSchemaHasType_sound checked.1)
            (inductionHypothesis checked.2)

/-- Check the exact argument list stored in a canonical occurrence row,
looking up its dependency sorts in the rule's unique binding declaration. -/
def checkStoredRowArguments (language : LanguageDef)
    (free : FreeTypeContext) (locals ambient : List TypeExpr)
    (spec : RuleBindingSpec) (row : MetavariableOccurrence) : Bool :=
  match dependencies? spec row.name with
  | none => false
  | some dependencies =>
      checkOccurrenceArguments language free locals ambient
        row.arguments dependencies

/-- A successful stored-row check supplies the exact dependency list and
the ordered typing derivations consumed by executable substitution. -/
theorem checkStoredRowArguments_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {locals ambient : List TypeExpr}
    {spec : RuleBindingSpec} {row : MetavariableOccurrence}
    (checked : checkStoredRowArguments language free locals ambient
      spec row = true) :
    ∃ dependencies,
      dependencies? spec row.name = some dependencies ∧
      List.Forall₂
        (fun argument dependency =>
          HasType language free (locals ++ ambient) argument dependency)
        row.arguments dependencies := by
  unfold checkStoredRowArguments at checked
  cases lookup : dependencies? spec row.name with
  | none => simp [lookup] at checked
  | some dependencies =>
      exact ⟨dependencies, rfl,
        checkOccurrenceArguments_sound (by simpa [lookup] using checked)⟩

/-- Structural admission records the row's actual dependency declaration,
address depth, exact arity, and raw local scope. These are obtained from the
canonical rule rather than inferred from the first occurrence. -/
theorem admittedFor_row_details
    {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true)
    {row : MetavariableOccurrence}
    (member : row ∈ spec.occurrences) :
    ∃ dependencies depth,
      dependencies? spec row.name = some dependencies ∧
      occurrenceDepthAtSite? rule row.site row.path = some depth ∧
      row.arguments.length = dependencies.length ∧
      row.arguments.all (fun argument => argument.isGroundAt depth) = true := by
  have rowsPass : spec.occurrences.all (fun row =>
      occurrenceDeclared rule row &&
        match dependencies? spec row.name,
          occurrenceDepthAtSite? rule row.site row.path with
        | some dependencies, some depth =>
            row.arguments.length == dependencies.length &&
              row.arguments.all (fun argument => argument.isGroundAt depth)
        | _, _ => false) = true := by
    simp only [admittedFor, Bool.and_eq_true] at admitted
    tauto
  have rowPass := List.all_eq_true.mp rowsPass row member
  simp only [Bool.and_eq_true] at rowPass
  cases dependencyLookup : dependencies? spec row.name with
  | none => simp [dependencyLookup] at rowPass
  | some dependencies =>
      cases depthLookup : occurrenceDepthAtSite? rule row.site row.path with
      | none => simp [dependencyLookup, depthLookup] at rowPass
      | some depth =>
          simp only [dependencyLookup, depthLookup, Bool.and_eq_true,
            beq_iff_eq] at rowPass
          exact ⟨dependencies, depth, rfl, rfl,
            rowPass.2.1, rowPass.2.2⟩

/-- Sorted row admission refines structural admission with an actual
rest-aware typing derivation for every supplied argument. -/
theorem admittedFor_row_sortedArguments
    {language : LanguageDef} {free : FreeTypeContext}
    {locals ambient : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true)
    {row : MetavariableOccurrence}
    (member : row ∈ spec.occurrences)
    (checked : checkStoredRowArguments language free locals ambient
      spec row = true) :
    ∃ dependencies depth,
      dependencies? spec row.name = some dependencies ∧
      occurrenceDepthAtSite? rule row.site row.path = some depth ∧
      row.arguments.length = dependencies.length ∧
      row.arguments.all (fun argument => argument.isGroundAt depth) = true ∧
      List.Forall₂
        (fun argument dependency =>
          HasType language free (locals ++ ambient) argument dependency)
        row.arguments dependencies := by
  obtain ⟨dependencies, depth, lookup, siteDepth, arity,
      rawScoped⟩ := admittedFor_row_details admitted member
  obtain ⟨checkedDependencies, checkedLookup, typed⟩ :=
    checkStoredRowArguments_sound checked
  have same : checkedDependencies = dependencies := by
    exact Option.some.inj (checkedLookup.symm.trans lookup)
  subst checkedDependencies
  exact ⟨dependencies, depth, lookup, siteDepth, arity, rawScoped, typed⟩

/-- Both executable address forms use the same sorted argument contract.
The typed address supplies the exact local binder-sort list and runtime
depth; this check supplies the list theorem required by substitution. -/
theorem TypedOccurrenceAt.instantiateChecked
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    {binderPrefix : List TypeExpr} {path : List Nat} {name : String}
    (typed : TypedOccurrenceAt language free bound pattern
      rootType binderPrefix path name)
    {dependencies : List TypeExpr} {body : Pattern}
    {resultType : TypeExpr} {arguments : List Pattern}
    (bodyTyped : HasType language free
      (dependencies ++ bound) body resultType)
    (argumentsChecked : checkOccurrenceArguments language free
      binderPrefix bound arguments dependencies = true) :
    ∃ instantiated,
      occurrenceDepthAt? pattern path 0 = some binderPrefix.length ∧
      instantiateValue?
        { dependencies, ambient := bound.length, body }
        bound.length binderPrefix.length arguments = some instantiated ∧
      HasType language free (binderPrefix ++ bound)
        instantiated resultType :=
  typed.instantiateCaptured bodyTyped
    (checkOccurrenceArguments_sound argumentsChecked)

/-- The canonical stored row, its actual typed rule site, and sorted row
checking feed the executable value instantiator without re-entering an
independent argument list. The matcher must still provide the captured value
with the stated dependency and ambient typing. -/
theorem TypedOccurrenceAt.instantiateAdmittedRow
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    {binderPrefix : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {row : MetavariableOccurrence}
    (typed : TypedOccurrenceAt language free bound pattern
      rootType binderPrefix row.path row.name)
    (site : sitePattern? rule row.site = some pattern)
    (admitted : admittedFor rule spec = true)
    (member : row ∈ spec.occurrences)
    {dependencies : List TypeExpr}
    (declared : dependencies? spec row.name = some dependencies)
    (checked : checkStoredRowArguments language free binderPrefix bound
      spec row = true)
    {body : Pattern} {resultType : TypeExpr}
    (bodyTyped : HasType language free
      (dependencies ++ bound) body resultType) :
    ∃ result,
      (sitePattern? rule row.site).bind
        (occurrenceDepthAt? · row.path 0) = some binderPrefix.length ∧
      instantiateValue?
        { dependencies, ambient := bound.length, body }
        bound.length binderPrefix.length row.arguments = some result ∧
      HasType language free (binderPrefix ++ bound)
        result resultType := by
  obtain ⟨checkedDependencies, _, checkedLookup, _, _, _,
      argumentsTyped⟩ :=
    admittedFor_row_sortedArguments admitted member checked
  have same : checkedDependencies = dependencies :=
    Option.some.inj (checkedLookup.symm.trans declared)
  subst checkedDependencies
  obtain ⟨result, runtimeDepth, executed, resultTyped⟩ :=
    typed.instantiateCaptured bodyTyped argumentsTyped
  exact ⟨result, by simpa [site] using runtimeDepth,
    executed, resultTyped⟩

/-- Typing judgment on the actual runtime capture carrier. Dependency and
ambient contexts are checked as data in the value, not reconstructed from an
occurrence depth. Matcher soundness must produce this judgment. -/
def ContextualValueHasType (language : LanguageDef)
    (free : FreeTypeContext) (dependencies ambient : List TypeExpr)
    (resultType : TypeExpr) (value : ContextualValue) : Prop :=
  value.dependencies = dependencies ∧
    value.ambient = ambient.length ∧
    HasType language free (dependencies ++ ambient)
      value.body resultType

/-- The admitted-row law consumes an actual captured runtime value once its
context metadata and body have been typed. The result is the term returned by
the same `instantiateValue?` call used in execution. -/
theorem TypedOccurrenceAt.instantiateAdmittedCapturedValue
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {rootType : TypeExpr}
    {binderPrefix : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {row : MetavariableOccurrence}
    (typed : TypedOccurrenceAt language free bound pattern
      rootType binderPrefix row.path row.name)
    (site : sitePattern? rule row.site = some pattern)
    (admitted : admittedFor rule spec = true)
    (member : row ∈ spec.occurrences)
    {dependencies : List TypeExpr}
    (declared : dependencies? spec row.name = some dependencies)
    (checked : checkStoredRowArguments language free binderPrefix bound
      spec row = true)
    {value : ContextualValue} {resultType : TypeExpr}
    (valueTyped : ContextualValueHasType language free
      dependencies bound resultType value) :
    ∃ result,
      (sitePattern? rule row.site).bind
        (occurrenceDepthAt? · row.path 0) = some binderPrefix.length ∧
      instantiateValue? value bound.length binderPrefix.length
        row.arguments = some result ∧
      HasType language free (binderPrefix ++ bound)
        result resultType := by
  cases value with
  | mk actualDependencies actualAmbient body =>
      obtain ⟨dependenciesEq, ambientEq, bodyTyped⟩ := valueTyped
      dsimp only [ContextualValueHasType] at dependenciesEq ambientEq bodyTyped
      subst actualDependencies
      subst actualAmbient
      exact typed.instantiateAdmittedRow site admitted member declared
        checked bodyTyped

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
