import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.LiteralPaths

/-! # Checked literal phases of the fixed and generated main clauses -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RowPhases

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration

abbrev Rule := ProgramBinders.Equation MSig [] ()

def mainPhases : List String := ["hd-seek", "hd-plug", "hd-root", "hd-eval", "hd-value", "hd-resume"]

theorem fixed_checked : ContextRules.fixed.all
    (fun rule => (LiteralPaths.symbolAt rule.lhs [1, 0]).any fun phase => decide (phase ∈ mainPhases)) = true := by
  decide +kernel

theorem fixed_phase {rule : Rule} (member : rule ∈ ContextRules.fixed) :
    ∃ phase ∈ mainPhases, LiteralPaths.symbolAt rule.lhs [1, 0] = some phase := by
  have checked := List.all_eq_true.mp fixed_checked rule member
  simp only [Option.any_eq_true, decide_eq_true_eq] at checked
  obtain ⟨phase, found, inside⟩ := checked
  exact ⟨phase, inside, found⟩

theorem row_phase {entry : Σ slots : Nat, Tower.Tm slots × Tower.Tm slots}
    {rule : Rule} (compiled : RowCompiler.row entry = some rule) :
    LiteralPaths.symbolAt rule.lhs [1, 0] = some "hd-root" ∧
      LiteralPaths.symbolAt rule.rhs [1, 0] = some "hd-subst-env" := by
  unfold RowCompiler.row at compiled
  split at compiled
  · split at compiled
    · cases compiled
    · cases compiled
      exact ⟨rfl, rfl⟩
  · cases compiled

theorem authored_phase {dev : NativeTypesOnTheStep.Computing.Definitions.Development}
    (built : Compiled dev) {rule : Rule} (member : rule ∈ built.authored) :
    LiteralPaths.symbolAt rule.lhs [1, 0] = some "hd-root" := by
  obtain ⟨entry, _, compiled⟩ := RowCompilation.reflects_member built.compiled member
  exact (row_phase compiled).1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RowPhases
