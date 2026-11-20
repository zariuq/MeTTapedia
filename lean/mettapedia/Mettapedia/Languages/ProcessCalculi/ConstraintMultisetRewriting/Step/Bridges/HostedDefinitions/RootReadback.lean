import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RootRewrites
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TermViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HelperPending

/-!
# Every selected root computation is a directed native reduction

The native substitution is recovered from the actual generated row match.
Primitive beta and row application enter the finite substitution helper;
projections return directly. A root selection therefore earns a source step
before its administrative episode is composed with context reconstruction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RootReadback

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

@[simp] theorem root_eq (a b k l : MClosed) :
    rootC a k = rootC b l ↔ a = b ∧ k = l := by
  simp [rootC, activeC, DataEmbedding.nodeC_eq_iff]

theorem primitive {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (input : Tower.Tm n) (continuation next : MClosed)
    (step : PrimitiveCases.Case (rootC (encodeTm input) continuation) next) :
    ∃ output : Tower.Tm n, StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) input output ∧
      (HelperPending.Pending output continuation next ∨ next = resumeC (encodeTm output) continuation) := by
  generalize same : rootC (encodeTm input) continuation = current at step
  cases step with
  | beta body argument k =>
      obtain ⟨encoded, rfl⟩ := (root_eq _ _ _ _).mp same
      obtain ⟨function, argument, rfl, functionCode, rfl⟩ := PatternReadback.encoded_app encoded.symm
      obtain ⟨body, rfl, rfl⟩ := TermViews.lam_of_code functionCode
      refine ⟨inst0 argument body, .betaPi body argument, .inl ?_⟩
      apply HelperPending.initial
      · exact RuntimeSubstitution.zero_internal _ _ _ _
      · simpa only [quoteRaw_rawTm, quoteRaw_substituteZero] using
          RuntimeSubstitution.zero_runs (rawTm argument) 0 (rawTm body) continuation
  | first left right k =>
      obtain ⟨encoded, rfl⟩ := (root_eq _ _ _ _).mp same
      obtain ⟨subject, rfl, subjectCode⟩ := TermViews.fst_of_code encoded.symm
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pair_of_code subjectCode
      exact ⟨left, .betaSigmaFst left right, .inr rfl⟩
  | second left right k =>
      obtain ⟨encoded, rfl⟩ := (root_eq _ _ _ _).mp same
      obtain ⟨subject, rfl, subjectCode⟩ := TermViews.snd_of_code encoded.symm
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pair_of_code subjectCode
      exact ⟨right, .betaSigmaSnd left right, .inr rfl⟩

theorem authored {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (input : Tower.Tm n) (continuation next : MClosed)
    (entry : RowCompilation.Entry) (selected : entry ∈ Vectors.vectorEquations ++ built.nativeRows)
    {rule : ProgramBinders.Equation MSig [] ()} (compiled : RowCompiler.row entry = some rule)
    (answered : ProgramBinders.Answers rule (rootC (encodeTm input) continuation) next) :
    ∃ output : Tower.Tm n, StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) input output ∧
      HelperPending.Pending output continuation next := by
  obtain ⟨substitution, starts, rfl⟩ := RowReadback.compiled_row_reflects entry compiled input continuation next answered
  have covered : DeclarationCheck.coveredB entry.2.1 entry.2.2 = true := by
    unfold RowCompiler.row at compiled
    split at compiled
    · assumption
    · cases compiled
  refine ⟨subst substitution entry.2.2, ?_, ?_⟩
  · rw [← starts]
    exact .root ((RootRewrites.presentation built).sound selected substitution)
  · apply HelperPending.initial
    · exact RuntimeSubstitution.environment_internal _ _ _
    · simpa only [RuntimeSubstitution.encodeRawEnv_environmentC,
        RowInstances.padded_right entry.2.1 entry.2.2 substitution covered] using
        RuntimeSubstitution.scoped_environment_runs (RowInstances.padded entry.2.1 substitution) entry.2.2 continuation

theorem of_step {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (input : Tower.Tm n) (continuation next : MClosed)
    (step : ProgramBinders.Rewrites built.rules.get (rootC (encodeTm input) continuation) next) :
    ∃ output : Tower.Tm n, StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) input output ∧
      (HelperPending.Pending output continuation next ∨ next = resumeC (encodeTm output) continuation) := by
  have classification := ProgramCases.at_main_phase built (phase := "hd-root") rfl (by decide) step
  cases classification with
  | primitive edge => exact primitive built input continuation next edge
  | authored entry selected rule compiled answered =>
      obtain ⟨output, reduced, pending⟩ := authored built input continuation next entry selected compiled answered
      exact ⟨output, reduced, .inl pending⟩
  | traversal edge =>
      generalize same : rootC (encodeTm input) continuation = current at edge
      cases edge <;> simp [rootC, seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same
  | driver edge =>
      generalize same : rootC (encodeTm input) continuation = current at edge
      cases edge <;> simp [rootC, evaluateC, valueC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RootReadback
