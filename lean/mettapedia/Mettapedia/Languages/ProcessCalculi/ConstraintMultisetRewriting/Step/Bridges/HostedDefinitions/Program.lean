import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramHeads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionHeads

/-!
# The finite source program compiled from an actual checked development

The result keeps the precise authored native table and its compiled equation
list, with their computed identities. Its fixed context/value rules and actual
substitution helpers are then ordinary equations in the same source program.
The compilation certificate records construction, not an operational theorem;
operation correspondence is established separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

structure Compiled (dev : Definitions.Development) where
  nativeRows : AlgebraicSchema.SchemaTable Tower.Head
  native : Definitions.devRules dev = some nativeRows
  authored : List (ProgramBinders.Equation MSig [] ())
  compiled : RowCompiler.rows (Vectors.vectorEquations ++ nativeRows) = some authored

def compile (dev : Definitions.Development) : Option (Compiled dev) :=
  match native : Definitions.devRules dev with
  | none => none
  | some rows =>
      match generated : RowCompiler.rows (Vectors.vectorEquations ++ rows) with
      | none => none
      | some authored => some ⟨rows, native, authored, generated⟩

def Compiled.rules {dev : Definitions.Development} (built : Compiled dev) :
    List (ProgramBinders.Equation MSig [] ()) :=
  ProgramLayout.rows RuntimeSubstitution.rules built.authored

def Compiled.program {dev : Definitions.Development} (built : Compiled dev) :
    SourceLanguage.Program (BinderCore.keys built.rules) [] () MTy := BinderCore.program built.rules

theorem Compiled.separated {dev : Definitions.Development} (built : Compiled dev) :
    HeadSeparated built.rules activeTag doneTag :=
  ProgramHeads.assembled RuntimeSubstitution.rules built.authored
    (fun rule member => ⟨(RuntimeSubstitution.rules_heads rule member).1,
      .inl (RuntimeSubstitution.rules_heads rule member).2⟩)
    (ProgramHeads.rows built.compiled)

theorem checked_compiles (dev : Definitions.Development) (checked : Definitions.devCheck dev = true) :
    ∃ built, compile dev = some built := by
  obtain ⟨nativeRows, native, _, _, _⟩ := Definitions.devCheck_parts checked
  obtain ⟨authored, generated⟩ := RowCompiler.checked_development_compiles dev checked
  rw [RowCompiler.development, native, Option.bind_some] at generated
  unfold compile
  split
  · rename_i absent
    rw [native] at absent
    cases absent
  · rename_i rows found
    rw [native] at found
    cases found
    split
    · rename_i absent
      rw [generated] at absent
      cases absent
    · rename_i result found
      rw [generated] at found
      cases found
      exact ⟨_, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
