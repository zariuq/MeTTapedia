import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalGroundingPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompilation

/-!
# Actual generated native rows preserve ground source calls

The environment helper receives only slots used on the left, with literal
padding elsewhere. Equality of left instances determines those used slots
and the continuation, so every target family gets the same right instance.
The complete native body stays literal data, including beneath binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingRows

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

theorem generated_grounding (entry : RowCompilation.Entry)
    {rule : ProgramBinders.Equation MSig [] ()} (compiled : RowCompiler.row entry = some rule) :
    GroundRead.Grounding rule := by
  unfold RowCompiler.row at compiled
  split at compiled
  · cases patternBuilt : RowCompiler.pattern (fun index => slot index.castSucc) entry.2.1 with
    | none => rw [patternBuilt] at compiled; cases compiled
    | some pattern =>
        rw [patternBuilt] at compiled
        cases compiled
        dsimp only [GroundRead.Grounding, equation]
        intro X target first environment matched
        let second : Assignment (FoArity (entry.1 + 1)) target := GroundRead.valuesAt target environment
        change instantiate first (RowCompiler.active "hd-root" [pattern, slot (Fin.last entry.1)]) =
          instantiate second (RowCompiler.active "hd-root" [pattern, slot (Fin.last entry.1)]) at matched
        change instantiate first
            (RowCompiler.active "hd-subst-env" [RowCompiler.listTemplate (RowCompiler.environment entry.2.1),
              literal (encodeTm entry.2.2), slot (Fin.last entry.1)]) =
          instantiate second
            (RowCompiler.active "hd-subst-env" [RowCompiler.listTemplate (RowCompiler.environment entry.2.1),
              literal (encodeTm entry.2.2), slot (Fin.last entry.1)])
        simp only [RowCompiler.active] at matched
        simp only [RuleBuilder.instantiate_node, List.map_cons, List.map_nil] at matched
        have fields := Toolkit.tuple3_inj (Toolkit.tuple2_inj matched).2
        have recovered := NormalGroundingPatterns.recover_pattern entry.2.1
          (fun index => slot index.castSucc) patternBuilt first second fields.2.1
        have sameEnvironment :
            instantiate first (RowCompiler.listTemplate (RowCompiler.environment entry.2.1)) =
              instantiate second (RowCompiler.listTemplate (RowCompiler.environment entry.2.1)) := by
          apply NormalGroundingPatterns.lists_agree
          intro template member
          obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
          by_cases used : 0 < AlgebraicSchema.variableMultiplicity index entry.2.1
          · rw [if_pos used]
            exact recovered index used
          · rw [if_neg used]
            simp only [instantiate_literal]
        simp only [RowCompiler.active, RuleBuilder.instantiate_node, List.map_cons, List.map_nil,
          instantiate_literal, sameEnvironment, fields.2.2]
  · cases compiled

theorem compiled_grounding {table : AlgebraicSchema.SchemaTable Tower.Head}
    {compiled : List (ProgramBinders.Equation MSig [] ())}
    (built : RowCompiler.rows table = some compiled) :
    ∀ rule ∈ compiled, GroundRead.Grounding rule := by
  intro rule member
  obtain ⟨entry, _, generated⟩ := RowCompilation.reflects_member built member
  exact generated_grounding entry generated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingRows

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingRows.generated_grounding
