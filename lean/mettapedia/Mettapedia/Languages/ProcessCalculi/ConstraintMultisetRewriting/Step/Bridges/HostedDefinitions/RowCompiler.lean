import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleBuilder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ControlProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Extension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaMatching

/-!
# The actual development rows compiled to native-source equation templates

The existing checked table supplies its supported left-side grammar. Row
bodies retain the full native term grammar as literal AST data; they enter the
explicit environment-substitution helper instead of being mistaken for MeTTa
surface applications. The table order and duplicate occurrences are retained.
Slots unused on the left receive fixed padding, not fresh right-side holes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
namespace RowCompiler

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open RuleBuilder

/-- Only the left-side matching grammar is restricted, exactly as in the
existing executable schema matcher. No restriction is imposed on row bodies. -/
def pattern : {slots holes : Nat} → (Fin slots → Template holes) → Tower.Tm slots → Option (Template holes)
  | _, _, images, .var index => some (images index)
  | _, _, _, .const name => some (literal (encodeTm (.const name : Tower.Tm 0)))
  | _, _, _, .head level => some (literal (encodeTm (.head level : Tower.Tm 0)))
  | _, _, images, .app function argument => do
      let f ← pattern images function
      let a ← pattern images argument
      pure (node "prime-tm-app" [f, a])
  | _, _, images, .refl term => do
      let value ← pattern images term
      pure (node "prime-tm-refl" [value])
  | _, _, _, _ => none

def environment {slots : Nat} (left : Tower.Tm slots) : List (Template (slots + 1)) :=
  (List.finRange slots).map fun index =>
    if 0 < AlgebraicSchema.variableMultiplicity index left then slot index.castSucc
    else literal (encodeTm (.const .anonymous : Tower.Tm 0))

def listTemplate {holes : Nat} : List (Template holes) → Template holes
  | [] => node "prime-list-nil" []
  | first :: rest => node "prime-list-cons" [first, listTemplate rest]

def active {holes : Nat} (phase : String) (arguments : List (Template holes)) : Template holes :=
  node activeTag [node phase arguments]

/-- One original schema contributes one equation. Its continuation occupies
the extra final hole, separate from all native substitution slots. -/
def row (entry : Σ slots : Nat, Tower.Tm slots × Tower.Tm slots) :
    Option (ProgramBinders.Equation MSig [] ()) := do
  if DeclarationCheck.coveredB entry.2.1 entry.2.2 then
    match pattern (fun index => slot index.castSucc) entry.2.1 with
    | none => none
    | some lhs => some (equation
        (active "hd-root" [lhs, slot (Fin.last entry.1)])
        (active "hd-subst-env" [listTemplate (environment entry.2.1),
          literal (encodeTm entry.2.2), slot (Fin.last entry.1)]))
  else none

def rows (table : AlgebraicSchema.SchemaTable Tower.Head) : Option (List (ProgramBinders.Equation MSig [] ())) :=
  table.mapM row

/-- The vector library and the actual authored development rows, in their
existing order. Failure remains explicit outside the checked table class. -/
def development (dev : Definitions.Development) : Option (List (ProgramBinders.Equation MSig [] ())) :=
  (Definitions.devRules dev).bind fun authored => rows (Vectors.vectorEquations ++ authored)

theorem pattern_compiles {slots holes : Nat} (images : Fin slots → Template holes) (term : Tower.Tm slots)
    (supported : ExecutableSchemaMatching.supported term = true) : ∃ result, pattern images term = some result := by
  induction term with
  | var index => exact ⟨_, rfl⟩
  | const name => exact ⟨_, rfl⟩
  | head level => exact ⟨_, rfl⟩
  | app function argument ihf iha =>
      have parts : ExecutableSchemaMatching.supported function = true ∧
          ExecutableSchemaMatching.supported argument = true := by
        simpa only [ExecutableSchemaMatching.supported, Bool.and_eq_true] using supported
      obtain ⟨f, hf⟩ := ihf images parts.1
      obtain ⟨a, ha⟩ := iha images parts.2
      exact ⟨node "prime-tm-app" [f, a], by simp [pattern, hf, ha]⟩
  | refl term ih =>
      obtain ⟨value, found⟩ := ih images supported
      exact ⟨node "prime-tm-refl" [value], by simp [pattern, found]⟩
  | _ => cases supported

theorem constructor_pattern_supported {defined : DeclName → Prop} {slots : Nat} {flag : Bool}
    {term : Tower.Tm slots} (shape : ConstructorSystem.Pattern defined flag term) :
    ExecutableSchemaMatching.supported term = true := by
  induction shape with
  | var => rfl
  | const => rfl
  | app _ _ ihf iha => simp [ExecutableSchemaMatching.supported, ihf, iha]
  | refl _ ih => exact ih

theorem left_side_supported {defined : DeclName → Prop} {slots : Nat} {name : DeclName} {count : Nat}
    {term : Tower.Tm slots} (shape : ConstructorSystem.LeftSide defined term name count) :
    ExecutableSchemaMatching.supported term = true := by
  induction shape with
  | const => rfl
  | app _ argument ih =>
      simp [ExecutableSchemaMatching.supported, ih, constructor_pattern_supported argument]

theorem row_compiles (entry : Σ slots : Nat, Tower.Tm slots × Tower.Tm slots)
    (supported : ExecutableSchemaMatching.supported entry.2.1 = true)
    (covered : DeclarationCheck.coveredB entry.2.1 entry.2.2 = true) :
    ∃ result, row entry = some result := by
  obtain ⟨lhs, found⟩ := pattern_compiles (fun index => slot index.castSucc) entry.2.1 supported
  exact ⟨equation (active "hd-root" [lhs, slot (Fin.last entry.1)])
    (active "hd-subst-env" [listTemplate (environment entry.2.1), literal (encodeTm entry.2.2),
      slot (Fin.last entry.1)]), by simp [row, covered, found]⟩

theorem rows_compile (table : AlgebraicSchema.SchemaTable Tower.Head)
    (supported : ∀ entry ∈ table, ExecutableSchemaMatching.supported entry.2.1 = true ∧
      DeclarationCheck.coveredB entry.2.1 entry.2.2 = true) :
    ∃ result, rows table = some result := by
  induction table with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
      obtain ⟨first, hf⟩ := row_compiles entry (supported entry List.mem_cons_self).1 (supported entry List.mem_cons_self).2
      obtain ⟨later, hl⟩ := ih (fun entry member => supported entry (List.mem_cons_of_mem _ member))
      change rest.mapM row = some later at hl
      exact ⟨first :: later, by simp [rows, List.mapM_cons, hf, hl]⟩

theorem checked_development_compiles (dev : Definitions.Development) (checked : Definitions.devCheck dev = true) :
    ∃ result, development dev = some result := by
  obtain ⟨authored, found, _, _, tableChecked⟩ := Definitions.devCheck_parts checked
  have supported : ∀ entry ∈ Vectors.vectorEquations ++ authored,
      ExecutableSchemaMatching.supported entry.2.1 = true ∧
      DeclarationCheck.coveredB entry.2.1 entry.2.2 = true := by
    intro entry member
    obtain ⟨_, _, _, shape, _, coverage⟩ := DeclarationCheck.checkTable_rows tableChecked member
    refine ⟨left_side_supported shape, ?_⟩
    apply List.all_eq_true.mpr
    intro index _
    by_cases used : 0 < AlgebraicSchema.variableMultiplicity index entry.2.2
    · simp [used, coverage index used]
    · simp [used]
  obtain ⟨result, compiled⟩ := rows_compile (Vectors.vectorEquations ++ authored) supported
  exact ⟨result, by simp [development, found, compiled]⟩

end RowCompiler
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
