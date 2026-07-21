import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.CalibratedPriority
import Mettapedia.GSLT.LanguageDef.Gauthier.SkeletonTrace

/-!
# First mismatches as counterexample-guided repair witnesses

A non-censored first mismatch carries an index, agreement on all earlier
observations, and a failed observation at that index.  Against the E1 target
list this becomes a concrete expected value that the evaluator did not emit.
Completed postfix stack entries are authenticated by the existing parser
before this execution feedback is attached.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

/-- The information exposed by a non-censored first-mismatch observation. -/
structure FirstMismatchWitness (limit : ℕ) (agrees : ℕ → Prop) where
  index : ℕ
  index_lt : index < limit
  agreesBefore : ∀ i, i < index → agrees i
  failsAt : ¬ agrees index

noncomputable def firstMismatchWitnessOfDepthLt
    (limit : ℕ) (agrees : ℕ → Prop)
    (hdepth : firstMismatchDepth limit agrees < limit) :
    FirstMismatchWitness limit agrees where
  index := firstMismatchDepth limit agrees
  index_lt := hdepth
  agreesBefore := fun _i hi ↦ matches_before_firstMismatchDepth limit agrees hi
  failsAt := mismatch_at_firstMismatchDepth limit agrees hdepth

namespace Gauthier

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
open Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity

private theorem exists_listGet?_of_lt {values : List Int} {i : ℕ}
    (hi : i < values.length) : ∃ value, listGet? values i = some value := by
  induction values generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => exact ⟨head, by simp [listGet?]⟩
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          rcases ih hi with ⟨value, hvalue⟩
          exact ⟨value, by simpa [listGet?]⟩

/-- Counterexample-guided repair record for the actual evaluator.  The
expected term is authenticated by the target list; every earlier term
matched; the expected term at `index` did not. -/
structure E1Counterexample (fuel : ℕ) (program : Prog) (target : List Int) where
  index : ℕ
  expected : Int
  index_lt : index < target.length
  expectedAt : listGet? target index = some expected
  earlierMatched : ∀ i, i < index → matchesTargetAt fuel program target i
  expectedNotEmitted : ¬ EmitsAt orgE1Signature fuel program
    (Int.ofNat index) expected

noncomputable def counterexampleOfFirstMismatch
    (fuel : ℕ) (program : Prog) (target : List Int)
    (hdepth : firstMismatchDepth fuel program target < target.length) :
    E1Counterexample fuel program target := by
  let index := firstMismatchDepth fuel program target
  have hindex : index < target.length := hdepth
  let expected := Classical.choose (exists_listGet?_of_lt hindex)
  have hexpected : listGet? target index = some expected :=
    Classical.choose_spec (exists_listGet?_of_lt hindex)
  have hfail : ¬ matchesTargetAt fuel program target index :=
    SemanticShaping.mismatch_at_firstMismatchDepth target.length
      (matchesTargetAt fuel program target) hdepth
  refine
    { index := index
      expected := expected
      index_lt := hindex
      expectedAt := hexpected
      earlierMatched := ?_
      expectedNotEmitted := ?_ }
  · intro i hi
    exact SemanticShaping.matches_before_firstMismatchDepth target.length
      (matchesTargetAt fuel program target) hi
  · intro hemits
    apply hfail
    intro value hvalue
    rw [hexpected] at hvalue
    cases hvalue
    exact hemits

theorem probe_counterexample_index_one :
    (counterexampleOfFirstMismatch 20 probeZeroAfterZero [0, 1]
      (by rw [probeZeroAfterZero_firstMismatch_is_one]; norm_num)).index = 1 := by
  change firstMismatchDepth 20 probeZeroAfterZero [0, 1] = 1
  exact probeZeroAfterZero_firstMismatch_is_one

theorem probe_counterexample_expected_one :
    (counterexampleOfFirstMismatch 20 probeZeroAfterZero [0, 1]
      (by rw [probeZeroAfterZero_firstMismatch_is_one]; norm_num)).expected = 1 := by
  let witness := counterexampleOfFirstMismatch 20 probeZeroAfterZero [0, 1]
    (by rw [probeZeroAfterZero_firstMismatch_is_one]; norm_num)
  change witness.expected = 1
  have hindex : witness.index = 1 := by
    change firstMismatchDepth 20 probeZeroAfterZero [0, 1] = 1
    exact probeZeroAfterZero_firstMismatch_is_one
  have hexpected := witness.expectedAt
  rw [hindex] at hexpected
  simp [listGet?] at hexpected
  exact hexpected.symm

end Gauthier

/-! ## Authenticated completed postfix entries -/

namespace Postfix

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonTrace

/-- A program is a completed postfix stack entry only after the actual raw
recognizer has constructed it. -/
def CompletedStackEntry (tokens : List Tok) (stack : List Prog) (program : Prog) : Prop :=
  recognizeRawStack orgMemoSignature tokens [] = some stack ∧ program ∈ stack

/-- Execution feedback attached to an authenticated stack entry. -/
noncomputable def completedEntryFeedback
    (fuel : ℕ) (target : List Int) (program : Prog) : ℕ :=
  Gauthier.firstMismatchDepth fuel program target

/-- Parser provenance and bounded execution feedback travel together: the
recognized stack serializes exactly the consumed tokens, and every completed
entry receives a censored depth within the target length. -/
theorem completedStackEntry_has_authenticatedFeedback
    {tokens : List Tok} {stack : List Prog} {program : Prog}
    (hentry : CompletedStackEntry tokens stack program)
    (fuel : ℕ) (target : List Int) :
    stackTokens stack = tokens ∧
      completedEntryFeedback fuel target program ≤ target.length := by
  constructor
  · have htokens := recognizeRawStack_stackTokens orgMemoSignature
      tokens [] stack hentry.1
    simpa [stackTokens] using htokens
  · exact Gauthier.firstMismatchDepth_le_targetLength fuel program target

/-- Positive fixture: the constant-zero operator is a completed singleton
stack entry under the actual `org.memo` recognizer. -/
theorem zero_is_completedStackEntry :
    CompletedStackEntry [0] [Org.z] Org.z := by
  constructor
  · rfl
  · simp

end Postfix

#print axioms firstMismatchWitnessOfDepthLt
#print axioms Gauthier.counterexampleOfFirstMismatch
#print axioms Gauthier.probe_counterexample_index_one
#print axioms Postfix.completedStackEntry_has_authenticatedFeedback
#print axioms Postfix.zero_is_completedStackEntry

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
