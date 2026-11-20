import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PatternReadback

/-!
# An actual generated-row firing reconstructs the native schema instance

The matching environment comes from the real source equation. Used slots are
read back at the actual native ambient scope; unused slots are padded only
where their none query is proved. The generated target is the exact runtime
substitution request, not a semantic reduction supplied to its admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RowReadback

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open RuleBuilder

theorem environment_of_used {slots ambient : Nat} (left : Tower.Tm slots)
    (substitution : Sub Tower.Head slots ambient) (environment : Fin (slots + 1) → MClosed)
    (used : ∀ index, 0 < AlgebraicSchema.variableMultiplicity index left →
      environment index.castSucc = encodeTm (substitution index)) :
    materialize environment (RowCompiler.listTemplate (RowCompiler.environment left)) =
      environmentC (DataEmbedding.rawEnvironment (RowInstances.padded left substitution)) := by
  rw [RowInstances.materialize_list]
  unfold environmentC
  apply congrArg listC
  apply List.ext_getElem
  · simp [RowCompiler.environment, DataEmbedding.rawEnvironment]
  · intro index smallLeft smallRight
    have bound : index < slots := by simpa [DataEmbedding.rawEnvironment] using smallRight
    simp [RowCompiler.environment, DataEmbedding.rawEnvironment, RowInstances.padded]
    split
    · rename_i occurs
      rw [materialize_slot]
      change environment (Fin.castSucc (⟨index, bound⟩ : Fin slots)) = encodeTm (substitution ⟨index, bound⟩)
      exact used ⟨index, bound⟩ occurs
    · simp

theorem compiled_row_reflects (entry : Σ slots : Nat, Tower.Tm slots × Tower.Tm slots)
    {rule : ProgramBinders.Equation MSig [] ()} (compiled : RowCompiler.row entry = some rule)
    {ambient : Nat} (input : Tower.Tm ambient) (continuation result : MClosed)
    (answered : ProgramBinders.Answers rule (rootC (encodeTm input) continuation) result) :
    ∃ substitution : Sub Tower.Head entry.1 ambient,
      subst substitution entry.2.1 = input ∧
      result = substituteEnvironmentC
        (environmentC (DataEmbedding.rawEnvironment (RowInstances.padded entry.2.1 substitution)))
        (encodeTm entry.2.2) continuation := by
  unfold RowCompiler.row at compiled
  split at compiled
  · cases found : RowCompiler.pattern (fun index => slot index.castSucc) entry.2.1 with
    | none => rw [found] at compiled; cases compiled
    | some lhs =>
      rw [found] at compiled
      cases compiled
      obtain ⟨environment, matched, produced⟩ := (RuleBuilder.answers_iff _ _ _ _).mp answered
      simp only [RowCompiler.active, materialize_node, materialize_slot, materialize_literal,
        List.map_cons, List.map_nil, rootC, activeC] at matched produced
      have outer := (DataEmbedding.nodeC_eq_iff.mp matched).2
      have phase := (List.cons.inj outer).1
      have fields := (DataEmbedding.nodeC_eq_iff.mp phase).2
      obtain ⟨reads, rest⟩ := List.cons.inj fields
      have passed := (List.cons.inj rest).1
      obtain ⟨substitution, native, used⟩ :=
        PatternReadback.native_substitution_of_match entry.2.1 environment found reads
      refine ⟨substitution, native, ?_⟩
      have encodedEnv := environment_of_used entry.2.1 substitution environment used
      rw [encodedEnv, passed] at produced
      exact produced.symm
  · cases compiled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RowReadback
