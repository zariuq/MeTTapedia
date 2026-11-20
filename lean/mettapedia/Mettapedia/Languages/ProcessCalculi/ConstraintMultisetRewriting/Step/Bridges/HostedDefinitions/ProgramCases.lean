import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TraversalCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PrimitiveCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.DriverCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HelperIsolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompilation

/-!
# Actual program steps separated by their originating clause

The classification reads the actual source equation selected by a firing.
These propositions describe possible endpoints; they do not recover event
multiplicity or clause ordinals from proof-irrelevant existence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramCases

open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

inductive Main {dev : Definitions.Development} (built : Compiled dev) (before after : MClosed) : Prop
  | traversal (step : TraversalCases.Case before after)
  | primitive (step : PrimitiveCases.Case before after)
  | driver (step : DriverCases.Case before after)
  | authored (entry : Σ slots : Nat, Tower.Tm slots × Tower.Tm slots)
      (selected : entry ∈ Vectors.vectorEquations ++ built.nativeRows)
      (rule : ProgramBinders.Equation MSig [] ())
      (compiled : RowCompiler.row entry = some rule)
      (answered : ProgramBinders.Answers rule before after)

theorem rewrite_of_member {rules : List (ProgramBinders.Equation MSig [] ())}
    {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ rules) {before after : MClosed}
    (answered : ProgramBinders.Answers rule before after) : ProgramBinders.Rewrites rules.get before after := by
  obtain ⟨index, same⟩ := List.mem_iff_get.mp member
  exact ⟨index, by simpa only [same] using answered⟩

theorem helper_has_internal_source {before after : MClosed}
    (step : RuntimeSubstitution.Step before after) : RuntimeSubstitution.Internal before := by
  obtain ⟨index, answered⟩ := step
  have member := List.get_mem RuntimeSubstitution.rules index
  have checked : ∀ rule ∈ RuntimeSubstitution.rules,
      ∃ phase, LiteralPaths.symbolAt rule.lhs [1, 0] = some phase := by
    intro rule inside
    have total : RuntimeSubstitution.rules.all
        (fun rule => (LiteralPaths.symbolAt rule.lhs [1, 0]).isSome) = true := by decide +kernel
    have yes := List.all_eq_true.mp total rule inside
    cases named : LiteralPaths.symbolAt rule.lhs [1, 0] with
    | none => rw [named] at yes; cases yes
    | some phase => exact ⟨phase, rfl⟩
  obtain ⟨phase, named⟩ := checked _ member
  exact ⟨phase, answered_phase named answered,
    List.mem_filterMap.mpr ⟨_, member, named⟩⟩

theorem step_cases {dev : Definitions.Development} (built : Compiled dev) {before after : MClosed}
    (step : ProgramBinders.Rewrites built.rules.get before after) :
    Main built before after ∨ RuntimeSubstitution.Step before after := by
  obtain ⟨index, answered⟩ := step
  have member := List.get_mem built.rules index
  simp only [Compiled.rules, ProgramLayout.rows, List.mem_append, ContextRules.fixed] at member
  rcases member with (((traversal | primitive) | driver) | helper) | authored
  · exact .inl (.traversal (TraversalCases.of_step (rewrite_of_member traversal answered)))
  · exact .inl (.primitive (PrimitiveCases.of_step (rewrite_of_member primitive answered)))
  · exact .inl (.driver (DriverCases.of_step (rewrite_of_member driver answered)))
  · exact .inr (rewrite_of_member helper answered)
  · obtain ⟨entry, selected, compiled⟩ := RowCompilation.reflects_member built.compiled authored
    exact .inl (.authored entry selected _ compiled answered)

theorem at_main_phase {dev : Definitions.Development} (built : Compiled dev) {before after : MClosed}
    {phase : String} (named : RuntimeSubstitution.phaseOf before = some phase)
    (main : phase ∈ RowPhases.mainPhases)
    (step : ProgramBinders.Rewrites built.rules.get before after) : Main built before after := by
  rcases step_cases built step with result | helper
  · exact result
  · obtain ⟨actual, observed, inside⟩ := helper_has_internal_source helper
    have same := Option.some.inj (named.symm.trans observed)
    subst actual
    exact False.elim (HelperIsolation.phase_palettes_disjoint inside main)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramCases
