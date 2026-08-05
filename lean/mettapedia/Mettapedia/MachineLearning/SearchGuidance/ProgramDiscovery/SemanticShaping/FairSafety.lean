import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.RepairBoundary
import Mettapedia.GSLT.LanguageDef.Gauthier.CertifiedMask

/-!
# Checker safety and fair baseline reachability

Semantic scores are permitted to reorder complete legal actions but never to
change checker acceptance.  A periodic two-queue scheduler gives every
baseline rank an explicit submission time while reserving a positive fraction
of submissions for the baseline queue.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

open Mettapedia.GSLT.LanguageDef.GauthierCertifiedMask
open Mettapedia.GSLT.LanguageDef.GauthierRefinement

/-! ## The actual Gauthier checker boundary -/

/-- Any complete semantic ranking is acceptance-equivalent to the underlying
Gauthier refinement checker.  The ranking cannot create acceptance. -/
theorem partialRanking_cannot_create_acceptance
    (ranking : orgMemoRoot.State → List orgMemoRoot.Action)
    (hcoverage : orgMemoRoot.ListsAllLegalActions ranking)
    {budget : ℕ} {trace : List orgMemoRoot.Action}
    {program : Mettapedia.GSLT.LanguageDef.GauthierE1.Prog} :
    orgMemoRoot.RankedAccepts ranking budget trace program ↔
      orgMemoRoot.Accepts budget trace program :=
  gauthierSoftRanking_always_safe ranking hcoverage

/-! ## Periodic two-queue scheduling -/

/-- Every block contains one baseline submission and `semanticSlots` semantic
submissions. -/
def queuePeriod (semanticSlots : ℕ) : ℕ := semanticSlots + 1

/-- The asymptotic baseline reservation represented exactly as a rational. -/
def baselineShare (semanticSlots : ℕ) : ℚ :=
  1 / (queuePeriod semanticSlots : ℚ)

theorem baselineShare_pos (semanticSlots : ℕ) :
    0 < baselineShare semanticSlots := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.zero_lt_succ semanticSlots

/-- Baseline positions are the first submission in each periodic block. -/
def isBaselineTime (semanticSlots time : ℕ) : Bool :=
  time % queuePeriod semanticSlots == 0

/-- A concrete two-queue enumerator.  Baseline items use one slot per block;
semantic items occupy all other slots. -/
def twoQueueCandidate {Candidate : Type*}
    (baseline semantic : List Candidate) (semanticSlots time : ℕ) : Option Candidate :=
  if isBaselineTime semanticSlots time then
    baseline[time / queuePeriod semanticSlots]?
  else
    semantic[time - time / queuePeriod semanticSlots - 1]?

theorem queuePeriod_pos (semanticSlots : ℕ) : 0 < queuePeriod semanticSlots := by
  simp [queuePeriod]

/-- The zero-based candidate at baseline rank `rank` is submitted after at
most the multiplicative slowdown `semanticSlots + 1`. -/
theorem twoQueueCandidate_mul_queuePeriod
    {Candidate : Type*} (baseline semantic : List Candidate)
    (semanticSlots rank : ℕ) :
    twoQueueCandidate baseline semantic semanticSlots
        (queuePeriod semanticSlots * rank) = baseline[rank]? := by
  have hperiod : 0 < queuePeriod semanticSlots := queuePeriod_pos semanticSlots
  simp [twoQueueCandidate, isBaselineTime, hperiod]

theorem baseline_rank_time_slowdown_bound (semanticSlots rank : ℕ) :
    queuePeriod semanticSlots * rank <
      queuePeriod semanticSlots * (rank + 1) := by
  exact (Nat.mul_lt_mul_left (queuePeriod_pos semanticSlots)).2
    (Nat.lt_succ_self rank)

/-- Positive fixture: with one semantic slot, the scheduler alternates
baseline and semantic candidates. -/
theorem alternating_twoQueue :
    twoQueueCandidate [10, 20] [30, 40] 1 0 = some 10 ∧
      twoQueueCandidate [10, 20] [30, 40] 1 1 = some 30 ∧
      twoQueueCandidate [10, 20] [30, 40] 1 2 = some 20 := by
  decide

/-- Negative fixture: a semantic-only scheduler can permanently omit a real
baseline candidate; the reservation theorem is therefore substantive. -/
theorem semanticOnly_can_omit_baseline_negativeExample :
    (42 : ℕ) ∈ [42] ∧ ∀ time : ℕ, ([7, 8][time]?).getD 0 ≠ 42 := by
  constructor
  · simp
  · intro time
    cases time <;> simp_all
    rename_i time
    cases time <;> simp_all

#print axioms partialRanking_cannot_create_acceptance
#print axioms baselineShare_pos
#print axioms twoQueueCandidate_mul_queuePeriod
#print axioms baseline_rank_time_slowdown_bound
#print axioms semanticOnly_can_omit_baseline_negativeExample

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
