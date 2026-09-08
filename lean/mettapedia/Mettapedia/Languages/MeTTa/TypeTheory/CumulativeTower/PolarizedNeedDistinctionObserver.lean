import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedProviderWorkload
import Mettapedia.Cybernetics.DistinctionCalculus.Weighted

/-!
# Distinction loss on the executed shared-provider workload

The two source programs use the actual inference provider and owned Need
machine. They return the same pair of native replies on every completed
branch, but their effect histories differ: shared selection correlates the
provider identities; fresh selection permits mixed identities.

Observing the first native reply pair therefore identifies two programs that
the complete event-frontier observer separates. On the uniform two-program
population, the resulting distortion is exactly 1/2. This is a measurement
under these declared observers, not a runtime probability or cost model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedDistinctionObserver

open Mettapedia.Cybernetics.DistinctionCalculus
open PolarizedNeedProviderWorkload
open PolarizedNeedInferenceService
open Presentation

def source (fresh : Bool) : Source := if fresh then freshWorkload else sharedWorkload

def observed (fresh : Bool) : List (Option (Tower.Tm 0) × List Event) :=
  observations scope 64 (source fresh)

def payloadReport (fresh : Bool) : Option (Option (Tower.Tm 0)) :=
  (observed fresh).head?.map Prod.fst

def eventReport (fresh : Bool) : List (List Event) := (observed fresh).map Prod.snd

theorem every_branch_retains_the_native_replies (fresh : Bool)
    (entry : Option (Tower.Tm 0) × List Event) (member : entry ∈ observed fresh) :
    entry.1 = some expectedPair := by
  cases fresh <;>
    simp only [observed, source, Bool.false_eq_true, if_false, if_true,
      shared_provider_correlates, fresh_provider_selects_independently,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem payloadReport_eq (fresh : Bool) : payloadReport fresh = some (some expectedPair) := by
  cases fresh <;>
    simp [payloadReport, observed, source, shared_provider_correlates,
      fresh_provider_selects_independently]

theorem eventReport_injective : Function.Injective eventReport := by
  intro x y same
  cases x <;> cases y
  · rfl
  · have counts := congrArg List.length same
    simp [eventReport, observed, source, shared_provider_correlates,
      fresh_provider_selects_independently] at counts
  · have counts := congrArg List.length same
    simp [eventReport, observed, source, shared_provider_correlates,
      fresh_provider_selects_independently] at counts
  · rfl

def fineObserver : Tolerance Bool := Tolerance.ofReport eventReport

def coarseObserver : Tolerance Bool := Tolerance.ofReport payloadReport

theorem fine_similarity (x y : Bool) :
    fineObserver.similarity x y = if x = y then 1 else 0 := by
  simp [fineObserver, Tolerance.ofReport, eventReport_injective.eq_iff]

theorem coarse_similarity (x y : Bool) : coarseObserver.similarity x y = 1 := by
  simp [coarseObserver, Tolerance.ofReport, payloadReport_eq]

theorem payload_identity_is_not_execution_identity :
    coarseObserver.Indistinguishable false true ∧ fineObserver.Apart false true := by
  constructor
  · rw [Tolerance.indistinguishable_iff_similarity_one, coarse_similarity]
  · norm_num [Tolerance.Apart, Tolerance.distance, fine_similarity]

def programPopulation : Distribution Bool where
  weight _ := 1 / 2
  nonnegative _ := by norm_num
  normalized := by norm_num

theorem measured_loss_of_execution_distinctions :
    programPopulation.distortion fineObserver coarseObserver id = 1 / 2 := by
  norm_num [Distribution.distortion, Distribution.pairAverage, programPopulation,
    fine_similarity, coarse_similarity]

/-- The coarser observer cannot be used as an isometry certificate for effects. -/
theorem payload_preservation_does_not_preserve_effects :
    payloadReport false = payloadReport true ∧
      ¬ (∀ x y, coarseObserver.similarity (id x) (id y) = fineObserver.similarity x y) := by
  refine ⟨by rw [payloadReport_eq, payloadReport_eq], ?_⟩
  intro falselyFine
  have bad := falselyFine false true
  norm_num [coarse_similarity, fine_similarity] at bad

/-! ## The requested theorem does not determine an article's admission -/

def article (valid : Bool) : RawInferenceService.Candidate :=
  if valid then acceptedCandidate else rejectedCandidate

def nativeVerdict (valid : Bool) : RawInferenceService.Verdict :=
  RawInferenceService.check MILCheckedChain.learned.target scope (article valid)

theorem nativeVerdict_computed (valid : Bool) : nativeVerdict valid = .checked valid := by
  cases valid
  · have decoded := congrArg RawInferenceService.decodeReply rejected_reply_computed
    simp only [checkedReply, rejectedReply, RawInferenceService.decode_encode_reply,
      Option.some.injEq] at decoded
    exact congrArg RawInferenceService.Reply.verdict decoded
  · have decoded := congrArg RawInferenceService.decodeReply accepted_reply_computed
    simp only [checkedReply, acceptedReply, RawInferenceService.decode_encode_reply,
      Option.some.injEq] at decoded
    exact congrArg RawInferenceService.Reply.verdict decoded

theorem article_requests_equal : (article false).request = (article true).request := rfl

def requestObserver : Tolerance Bool := Tolerance.ofReport fun valid => (article valid).request

def admissionObserver : Tolerance Bool := Tolerance.ofReport nativeVerdict

theorem same_request_different_admission :
    requestObserver.Indistinguishable false true ∧ admissionObserver.Apart false true := by
  constructor
  · exact (Tolerance.ofReport_indistinguishable _ _ _).mpr article_requests_equal
  · norm_num [Tolerance.Apart, Tolerance.distance, admissionObserver, Tolerance.ofReport,
      nativeVerdict_computed]

/-- No classifier that sees only the shared request can reproduce these
actual native checker verdicts. Inspecting the article is indispensable. -/
theorem admission_does_not_factor_through_request :
    ¬ ∃ classifier : RawInferenceService.Request → RawInferenceService.Verdict,
      ∀ valid, classifier (article valid).request = nativeVerdict valid := by
  rintro ⟨classifier, classifies⟩
  have same := congrArg classifier article_requests_equal
  rw [classifies, classifies, nativeVerdict_computed, nativeVerdict_computed] at same
  cases same

end PolarizedNeedDistinctionObserver
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
