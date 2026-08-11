import Mettapedia.PLN.Bridges.GSLT.InferenceControl

/-!
# Semantics-preserving guidance reductions

This module isolates optimizations that may reduce the physical cost of
evidence-guided inference without changing which candidate an exact policy
selects or which derivations the underlying GSLT admits.

The results are deliberately representation-independent:

* a strength-times-confidence score fuses to one rational expression;
* revision-indexed memo tables may retain exactly the entries outside a
  declared dependency cone;
* an additive scorer evaluates batches and revised worlds compositionally;
* certified lower bounds justify lazy evaluation;
* a covering shortlist justifies coarse-to-fine selection;
* bounded fallback embeds every baseline choice at a known finite index; and
* a break-even law states exactly when guidance overhead is repaid by avoided
  expansions.

None of these results authorizes an inference step.  They refine only the
controller that chooses among already-live occurrences.
-/

namespace Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization

open scoped Classical ENNReal

/-! ## Algebraic fusion of the PLN guidance score -/

namespace ScoreFusion

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The direct presentation used by the reference policy: posterior strength
times confidence with prior mass `prior`. -/
def referenceQuality (positive negative prior : K) : K :=
  let total := positive + negative
  if total = 0 then 0
  else (positive / total) * (total / (total + prior))

/-- The fused presentation.  It requires one addition chain and one division,
instead of two divisions followed by a multiplication. -/
def fusedQuality (positive negative prior : K) : K :=
  positive / (positive + negative + prior)

/-- Fusion is exact for every ordered field, including the zero-evidence case.
The positivity assumptions are the semantic validity conditions on evidence
counts and prior mass. -/
theorem referenceQuality_eq_fused
    (positive negative prior : K)
    (positive_nonnegative : 0 ≤ positive)
    (negative_nonnegative : 0 ≤ negative)
    (prior_positive : 0 < prior) :
    referenceQuality positive negative prior =
      fusedQuality positive negative prior := by
  unfold referenceQuality fusedQuality
  dsimp only
  by_cases total_zero : positive + negative = 0
  · have positive_zero : positive = 0 := by
      nlinarith
    simp [positive_zero]
  · have denominator_positive : 0 < positive + negative + prior := by
      nlinarith
    have denominator_ne : positive + negative + prior ≠ 0 :=
      ne_of_gt denominator_positive
    simp only [total_zero, if_false]
    field_simp [total_zero, denominator_ne]

/-- Exact quality comparison needs no division: positive denominators permit
cross multiplication.  This is the basis for an integer/rational comparator. -/
theorem fusedQuality_lt_iff_crossMultiply
    (firstPositive firstNegative secondPositive secondNegative prior : K)
    (firstPositive_nonnegative : 0 ≤ firstPositive)
    (firstNegative_nonnegative : 0 ≤ firstNegative)
    (secondPositive_nonnegative : 0 ≤ secondPositive)
    (secondNegative_nonnegative : 0 ≤ secondNegative)
    (prior_positive : 0 < prior) :
    fusedQuality firstPositive firstNegative prior <
        fusedQuality secondPositive secondNegative prior ↔
      firstPositive * (secondPositive + secondNegative + prior) <
        secondPositive * (firstPositive + firstNegative + prior) := by
  have first_denominator_positive :
      0 < firstPositive + firstNegative + prior := by
    nlinarith
  have second_denominator_positive :
      0 < secondPositive + secondNegative + prior := by
    nlinarith
  simpa [fusedQuality] using
    (div_lt_div_iff₀ first_denominator_positive
      second_denominator_positive)

/-- The zero-count branch really is covered by fusion, rather than hidden by a
nonzero side condition. -/
example : referenceQuality (0 : ℚ) 0 1 = fusedQuality 0 0 1 := by
  exact referenceQuality_eq_fused 0 0 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- Positive witness with the default unit prior. -/
example : referenceQuality (7 : ℚ) 0 1 = 7 / 8 := by
  norm_num [referenceQuality]

/-- Strength alone cannot replace the fused score: these two evidence packets
have equal strength but different confidence-sensitive quality. -/
theorem strength_only_is_not_quality :
    ((1 : ℚ) / (1 + 0) = 100 / (100 + 0)) ∧
      fusedQuality (1 : ℚ) 0 1 ≠ fusedQuality 100 0 1 := by
  constructor <;> norm_num [fusedQuality]

open Mettapedia.PLN.Evidence.EvidenceQuantale

/-- The reference score on the project's canonical evidence carrier. -/
noncomputable def binaryEvidenceReferenceQuality
    (prior : ℝ≥0∞) (evidence : BinaryEvidence) : ℝ≥0∞ :=
  BinaryEvidence.toStrength evidence *
    BinaryEvidence.toConfidence prior evidence

/-- The fused score on the canonical evidence carrier. -/
noncomputable def binaryEvidenceFusedQuality
    (prior : ℝ≥0∞) (evidence : BinaryEvidence) : ℝ≥0∞ :=
  evidence.pos / (evidence.total + prior)

/-- Fusion holds on finite `BinaryEvidence`, including zero evidence.  The
finiteness boundary is explicit because `ℝ≥0∞` deliberately contains `⊤`,
whose division conventions do not model a finite runtime counter. -/
theorem binaryEvidenceReferenceQuality_eq_fused
    (prior : ℝ≥0∞) (evidence : BinaryEvidence)
    (total_finite : evidence.total ≠ ⊤) :
    binaryEvidenceReferenceQuality prior evidence =
      binaryEvidenceFusedQuality prior evidence := by
  by_cases total_zero : evidence.total = 0
  · have components_zero : evidence.pos + evidence.neg = 0 := by
      simpa [BinaryEvidence.total] using total_zero
    have positive_zero : evidence.pos = 0 := (add_eq_zero.mp components_zero).1
    simp [binaryEvidenceReferenceQuality, binaryEvidenceFusedQuality,
      BinaryEvidence.toStrength, BinaryEvidence.toConfidence, total_zero,
      positive_zero]
  · unfold binaryEvidenceReferenceQuality binaryEvidenceFusedQuality
    rw [BinaryEvidence.toStrength]
    simp only [total_zero, if_false, BinaryEvidence.toConfidence]
    calc
      evidence.pos / evidence.total *
            (evidence.total / (evidence.total + prior)) =
          evidence.pos * evidence.total /
            (evidence.total * (evidence.total + prior)) := by
        symm
        exact ENNReal.mul_div_mul_comm (.inl total_zero) (.inl total_finite)
      _ = evidence.pos * evidence.total /
            ((evidence.total + prior) * evidence.total) := by
        rw [mul_comm evidence.total (evidence.total + prior)]
      _ = evidence.pos / (evidence.total + prior) :=
        ENNReal.mul_div_mul_right evidence.pos (evidence.total + prior)
          total_zero total_finite

end ScoreFusion

/-! ## Revision-keyed caches and dependency cones -/

namespace RevisionCache

universe uRevision uKey uValue

variable {Revision : Type uRevision} {Key : Type uKey} {Value : Type uValue}

/-- A semantic cache is indexed by the exact revision whose values it stores.
The functional lookup is the abstract interface; finite maps, arrays, tries,
and PathMap roots can all realize it. -/
structure Cache (Revision : Type uRevision) (Key : Type uKey)
    (Value : Type uValue) where
  revision : Revision
  lookup : Key → Value

/-- Every cached entry agrees with the direct evaluator at the named revision. -/
def Exact (evaluate : Revision → Key → Value)
    (cache : Cache Revision Key Value) : Prop :=
  ∀ key, cache.lookup key = evaluate cache.revision key

/-- A change set is sufficient when values outside it are revision-invariant. -/
def LocalUpdate (evaluate : Revision → Key → Value)
    (oldRevision newRevision : Revision) (changed : Key → Prop) : Prop :=
  ∀ key, ¬ changed key →
    evaluate newRevision key = evaluate oldRevision key

/-- Refresh changed keys and retain all other entries. -/
def refresh
    (evaluate : Revision → Key → Value) (newRevision : Revision)
    (changed : Key → Prop) [DecidablePred changed]
    (cache : Cache Revision Key Value) :
    Cache Revision Key Value where
  revision := newRevision
  lookup key :=
    if changed key then evaluate newRevision key else cache.lookup key

/-- Dependency-local refresh preserves exactness. -/
theorem refresh_exact
    (evaluate : Revision → Key → Value) (newRevision : Revision)
    (changed : Key → Prop) [DecidablePred changed]
    (cache : Cache Revision Key Value)
    (cache_exact : Exact evaluate cache)
    (local_update : LocalUpdate evaluate cache.revision newRevision changed) :
    Exact evaluate (refresh evaluate newRevision changed cache) := by
  intro key
  by_cases key_changed : changed key
  · simp [refresh, key_changed]
  · simp only [refresh, key_changed, if_false]
    rw [cache_exact key, local_update key key_changed]

/-- A cache lookup fails closed when its revision does not match the request. -/
def checkedLookup [DecidableEq Revision]
    (requested : Revision) (cache : Cache Revision Key Value) (key : Key) :
    Option Value :=
  if cache.revision = requested then some (cache.lookup key) else none

@[simp] theorem checkedLookup_at_own_revision [DecidableEq Revision]
    (cache : Cache Revision Key Value) (key : Key) :
    checkedLookup cache.revision cache key = some (cache.lookup key) := by
  simp [checkedLookup]

theorem checkedLookup_stale [DecidableEq Revision]
    (requested : Revision) (cache : Cache Revision Key Value) (key : Key)
    (stale : cache.revision ≠ requested) :
    checkedLookup requested cache key = none := by
  simp [checkedLookup, stale]

/-- A checked hit from an exact cache agrees with direct evaluation. -/
theorem checkedLookup_exact [DecidableEq Revision]
    (evaluate : Revision → Key → Value) (cache : Cache Revision Key Value)
    (cache_exact : Exact evaluate cache) (key : Key) :
    checkedLookup cache.revision cache key =
      some (evaluate cache.revision key) := by
  simp [checkedLookup, cache_exact key]

namespace Examples

def evaluate (revision : Nat × Nat) : Bool → Nat
  | true => revision.1
  | false => revision.2

def oldCache : Cache (Nat × Nat) Bool Nat where
  revision := (1, 2)
  lookup := evaluate (1, 2)

theorem oldCache_exact : Exact evaluate oldCache := by
  intro key
  rfl

def firstChanged : Bool → Prop
  | true => True
  | false => False

instance : DecidablePred firstChanged := fun key => by
  cases key
  · exact isFalse id
  · exact isTrue trivial

theorem update_is_local :
    LocalUpdate evaluate oldCache.revision (3, 2) firstChanged := by
  intro key unchanged
  cases key <;> simp [firstChanged, evaluate, oldCache] at unchanged ⊢

/-- Positive: only the affected key is recomputed. -/
theorem refreshedCache_exact :
    Exact evaluate (refresh evaluate (3, 2) firstChanged oldCache) :=
  refresh_exact evaluate (3, 2) firstChanged oldCache oldCache_exact
    update_is_local

/-- Negative: merely relabelling a stale cache as the new revision is wrong. -/
theorem relabel_without_refresh_is_not_exact :
    ¬ Exact evaluate
      ({ revision := (3, 2), lookup := oldCache.lookup } :
        Cache (Nat × Nat) Bool Nat) := by
  intro claimed
  have := claimed true
  norm_num [oldCache, evaluate] at this

end Examples

end RevisionCache

/-! ## Additive batched scoring -/

namespace Batch

universe uWorld uKey uValue

variable {World : Type uWorld} {Key : Type uKey} {Value : Type uValue}

/-- A scorer compatible with revision is an additive homomorphism in its world
argument, pointwise in the key. -/
structure AdditiveScorer (World : Type uWorld) (Key : Type uKey)
    (Value : Type uValue) [AddMonoid World] [AddMonoid Value] where
  score : World → Key → Value
  score_zero : ∀ key, score 0 key = 0
  score_add : ∀ first second key,
    score (first + second) key = score first key + score second key

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel

/-- Every admitted binary world model supplies an additive scorer directly. -/
noncomputable def ofBinaryWorldModel
    [EvidenceType World] [BinaryWorldModel World Key] :
    AdditiveScorer World Key BinaryEvidence where
  score world key :=
    BinaryWorldModel.evidence (State := World) (Query := Key) world key
  score_zero key := BinaryWorldModel.evidence_zero key
  score_add first second key := BinaryWorldModel.evidence_add first second key

variable [AddMonoid World] [AddMonoid Value]

/-- Evaluate a finite key batch against one immutable world revision. -/
def scoreBatch (scorer : AdditiveScorer World Key Value)
    (world : World) (keys : List Key) : List Value :=
  keys.map (scorer.score world)

@[simp] theorem scoreBatch_append
    (scorer : AdditiveScorer World Key Value) (world : World)
    (first second : List Key) :
    scoreBatch scorer world (first ++ second) =
      scoreBatch scorer world first ++ scoreBatch scorer world second := by
  simp [scoreBatch]

/-- Batch evaluation commutes with revision pointwise. -/
theorem scoreBatch_add
    (scorer : AdditiveScorer World Key Value)
    (first second : World) (keys : List Key) :
    scoreBatch scorer (first + second) keys =
      List.zipWith (· + ·) (scoreBatch scorer first keys)
        (scoreBatch scorer second keys) := by
  induction keys with
  | nil => rfl
  | cons key rest inductionHypothesis =>
      simp [scoreBatch, scorer.score_add, *]

@[simp] theorem scoreBatch_zero
    (scorer : AdditiveScorer World Key Value) (keys : List Key) :
    scoreBatch scorer 0 keys = keys.map (fun _ => 0) := by
  induction keys with
  | nil => rfl
  | cons key rest inductionHypothesis =>
      simp only [scoreBatch, List.map_cons]
      rw [scorer.score_zero]
      congr 1

end Batch

/-! ## Certified lazy and coarse-to-fine selection -/

namespace Selection

universe uCandidate uPriority

variable {Candidate : Type uCandidate} {Priority : Type uPriority}
variable [Preorder Priority]

/-- A candidate is an exact minimum of a finite occurrence list. -/
def IsWinner (priority : Candidate → Priority)
    (candidates : List Candidate) (winner : Candidate) : Prop :=
  winner ∈ candidates ∧
    ∀ candidate ∈ candidates, priority winner ≤ priority candidate

/-- Evidence sufficient to select exactly after evaluating only a subset.
Every unevaluated candidate has a certified lower bound, and the chosen exact
priority beats each such bound. -/
structure LazyCertificate [DecidableEq Candidate]
    (priority lowerBound : Candidate → Priority)
    (candidates evaluated : List Candidate) (winner : Candidate) : Prop where
  winner_evaluated : winner ∈ evaluated
  evaluated_subset : ∀ candidate ∈ evaluated, candidate ∈ candidates
  winner_le_evaluated :
    ∀ candidate ∈ evaluated, priority winner ≤ priority candidate
  lower_sound : ∀ candidate ∈ candidates, candidate ∉ evaluated →
    lowerBound candidate ≤ priority candidate
  winner_le_pending_bound :
    ∀ candidate ∈ candidates, candidate ∉ evaluated →
      priority winner ≤ lowerBound candidate

/-- Certified lazy evaluation selects the same semantic minimum as eager
evaluation. -/
theorem LazyCertificate.isWinner [DecidableEq Candidate]
    {priority lowerBound : Candidate → Priority}
    {candidates evaluated : List Candidate} {winner : Candidate}
    (certificate : LazyCertificate priority lowerBound candidates evaluated winner) :
    IsWinner priority candidates winner := by
  constructor
  · exact certificate.evaluated_subset winner certificate.winner_evaluated
  · intro candidate candidate_mem
    by_cases evaluated_mem : candidate ∈ evaluated
    · exact certificate.winner_le_evaluated candidate evaluated_mem
    · exact le_trans
        (certificate.winner_le_pending_bound candidate candidate_mem evaluated_mem)
        (certificate.lower_sound candidate candidate_mem evaluated_mem)

/-- Promote exactly one occurrence of a selected candidate to the frontier
head.  `erase` removes one matching occurrence, so multiplicity is preserved. -/
def promote [BEq Candidate] (winner : Candidate)
    (candidates : List Candidate) : List Candidate :=
  winner :: candidates.erase winner

/-- Promotion is an occurrence-preserving scheduler refinement. -/
theorem promote_perm [BEq Candidate] [LawfulBEq Candidate]
    {winner : Candidate} {candidates : List Candidate}
    (winner_mem : winner ∈ candidates) :
    List.Perm (promote winner candidates) candidates := by
  exact (List.perm_cons_erase winner_mem).symm

/-- A certified lazy choice therefore induces a lawful frontier permutation,
which is precisely the hypothesis consumed by the generic GSLT controller
soundness theorems. -/
theorem LazyCertificate.promote_perm
    [BEq Candidate] [LawfulBEq Candidate]
    {priority lowerBound : Candidate → Priority}
    {candidates evaluated : List Candidate} {winner : Candidate}
    (certificate : LazyCertificate priority lowerBound candidates evaluated winner) :
    List.Perm (promote winner candidates) candidates :=
  GuidanceOptimization.Selection.promote_perm certificate.isWinner.1

/-- A coarse shortlist covers the original frontier when every excluded
candidate is dominated by some retained candidate. -/
def Covers (priority : Candidate → Priority)
    (candidates shortlist : List Candidate) : Prop :=
  ∀ candidate ∈ candidates, candidate ∉ shortlist →
    ∃ retained ∈ shortlist, priority retained ≤ priority candidate

/-- The best acceptable candidate, rather than merely the best raw score. -/
def IsAcceptedWinner (acceptable : Candidate → Prop)
    (priority : Candidate → Priority) (candidates : List Candidate)
    (winner : Candidate) : Prop :=
  winner ∈ candidates ∧ acceptable winner ∧
    ∀ candidate ∈ candidates, acceptable candidate →
      priority winner ≤ priority candidate

/-- A coarse rejection pass is semantically safe when every discarded
candidate is known to be unacceptable. -/
def SafeRejection [DecidableEq Candidate]
    (acceptable : Candidate → Prop)
    (candidates shortlist : List Candidate) : Prop :=
  (∀ candidate ∈ shortlist, candidate ∈ candidates) ∧
    ∀ candidate ∈ candidates, candidate ∉ shortlist → ¬ acceptable candidate

/-- Exact search after a safe logical rejection pass is exact over the full
candidate language, even if a discarded invalid candidate had a better raw
priority. -/
theorem accepted_winner_of_safe_rejection
    [DecidableEq Candidate]
    {acceptable : Candidate → Prop} {priority : Candidate → Priority}
    {candidates shortlist : List Candidate} {winner : Candidate}
    (safe : SafeRejection acceptable candidates shortlist)
    (winner_shortlist : IsAcceptedWinner acceptable priority shortlist winner) :
    IsAcceptedWinner acceptable priority candidates winner := by
  refine ⟨safe.1 winner winner_shortlist.1,
    winner_shortlist.2.1, ?_⟩
  intro candidate candidate_mem candidate_acceptable
  by_cases retained : candidate ∈ shortlist
  · exact winner_shortlist.2.2 candidate retained candidate_acceptable
  · exact False.elim
      (safe.2 candidate candidate_mem retained candidate_acceptable)

/-- Exact minimization after a covering coarse pass equals exact minimization
over the whole frontier. -/
theorem winner_of_cover
    [DecidableEq Candidate]
    {priority : Candidate → Priority}
    {candidates shortlist : List Candidate} {winner : Candidate}
    (shortlist_subset : ∀ candidate ∈ shortlist, candidate ∈ candidates)
    (cover : Covers priority candidates shortlist)
    (shortlist_winner : IsWinner priority shortlist winner) :
    IsWinner priority candidates winner := by
  constructor
  · exact shortlist_subset winner shortlist_winner.1
  · intro candidate candidate_mem
    by_cases retained : candidate ∈ shortlist
    · exact shortlist_winner.2 candidate retained
    · obtain ⟨better, better_mem, better_le⟩ :=
        cover candidate candidate_mem retained
      exact le_trans (shortlist_winner.2 better better_mem) better_le

namespace Examples

def priority : Bool → Nat
  | false => 1
  | true => 3

def soundLowerBound : Bool → Nat
  | false => 1
  | true => 2

def lazyCertificate :
    LazyCertificate priority soundLowerBound [false, true] [false] false where
  winner_evaluated := by simp
  evaluated_subset := by simp
  winner_le_evaluated := by simp [priority]
  lower_sound := by
    intro candidate candidate_mem candidate_not_evaluated
    cases candidate <;> simp [priority, soundLowerBound] at candidate_not_evaluated ⊢
  winner_le_pending_bound := by
    intro candidate candidate_mem candidate_not_evaluated
    cases candidate <;> simp [priority, soundLowerBound] at candidate_not_evaluated ⊢

/-- Positive lazy witness. -/
theorem lazy_selects_exact_winner :
    IsWinner priority [false, true] false :=
  lazyCertificate.isWinner

/-- Negative: an unsound lower bound can certify the wrong pruning comparison.
The exact winner condition exposes the failure. -/
theorem wrong_lazy_choice_rejected :
    ¬ IsWinner priority [false, true] true := by
  simp [IsWinner, priority]

def acceptable : Bool → Prop
  | false => True
  | true => False

def adversarialPriority : Bool → Nat
  | false => 10
  | true => 0

theorem safe_rejection :
    SafeRejection acceptable [false, true] [false] := by
  constructor
  · simp
  · intro candidate candidate_mem candidate_not_retained
    cases candidate <;> simp [acceptable] at candidate_not_retained ⊢

theorem retained_is_accepted_winner :
    IsAcceptedWinner acceptable adversarialPriority [false] false := by
  simp [IsAcceptedWinner, acceptable, adversarialPriority]

/-- Positive logical-pruning witness: the rejected candidate has the better
raw priority, but it is not an admissible solution. -/
theorem safe_rejection_preserves_accepted_winner :
    IsAcceptedWinner acceptable adversarialPriority [false, true] false :=
  accepted_winner_of_safe_rejection safe_rejection
    retained_is_accepted_winner

/-- Negative: dropping an acceptable better candidate is not a safe rejection
and changes the accepted optimum. -/
theorem dropping_acceptable_candidate_is_rejected :
    ¬ SafeRejection (fun _ : Bool => True) [false, true] [false] := by
  intro safe
  exact safe.2 true (by simp) (by simp) trivial

def shortlistPriority : Fin 4 → Nat
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 7
  | ⟨3, _⟩ => 9

def allCandidates : List (Fin 4) := [0, 1, 2, 3]
def shortlist : List (Fin 4) := [0, 1]

theorem shortlist_covers :
    Covers shortlistPriority allCandidates shortlist := by
  intro candidate candidate_mem candidate_not_retained
  refine ⟨1, by simp [shortlist], ?_⟩
  fin_cases candidate <;>
    simp [shortlistPriority, shortlist] at candidate_not_retained ⊢

theorem shortlist_has_winner :
    IsWinner shortlistPriority shortlist 1 := by
  simp [IsWinner, shortlist, shortlistPriority]

/-- Positive coarse-to-fine witness. -/
theorem shortlist_winner_is_global :
    IsWinner shortlistPriority allCandidates 1 := by
  apply winner_of_cover (priority := shortlistPriority)
    (candidates := allCandidates) (shortlist := shortlist)
  · simp [allCandidates, shortlist]
  · exact shortlist_covers
  · exact shortlist_has_winner

/-- Negative: a shortlist that drops the true minimum without a dominating
retained candidate is not covering. -/
theorem dropping_minimum_breaks_cover :
    ¬ Covers shortlistPriority allCandidates [0, 2, 3] := by
  intro cover
  obtain ⟨retained, retained_mem, retained_le⟩ := cover 1 (by simp [allCandidates])
    (by simp)
  simp [shortlistPriority] at retained_mem retained_le
  rcases retained_mem with rfl | rfl | rfl <;> norm_num at retained_le

end Examples

end Selection

/-! ## Bounded fair fallback -/

namespace FairFallback

universe uChoice

/-- Run at most `quota` guided choices between successive baseline choices.
The baseline stream is sampled at a predictable subsequence. -/
def schedule (quota : Nat) (guided baseline : Nat → Choice) (tick : Nat) : Choice :=
  if tick % (quota + 1) = quota then baseline (tick / (quota + 1))
  else guided tick

/-- Every baseline choice occurs after a finite block of guided choices. -/
theorem schedule_embeds_baseline
    (quota index : Nat) (guided baseline : Nat → Choice) :
    schedule quota guided baseline ((quota + 1) * index + quota) =
      baseline index := by
  have quota_lt : quota < quota + 1 := Nat.lt_succ_self quota
  have block_positive : 0 < quota + 1 := Nat.succ_pos quota
  have modulus : ((quota + 1) * index + quota) % (quota + 1) = quota := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt quota_lt]
  have quotient : ((quota + 1) * index + quota) / (quota + 1) = index := by
    rw [Nat.mul_add_div block_positive, Nat.div_eq_of_lt quota_lt, add_zero]
  simp [schedule, modulus, quotient]

/-- Consequently every property reached by the baseline enumeration is also
reached by bounded fallback. -/
theorem eventually_of_baseline
    (quota : Nat) (guided baseline : Nat → Choice)
    (property : Choice → Prop) (index : Nat)
    (baseline_reaches : property (baseline index)) :
    ∃ tick, property (schedule quota guided baseline tick) := by
  refine ⟨(quota + 1) * index + quota, ?_⟩
  simpa [schedule_embeds_baseline] using baseline_reaches

/-- Negative: unrestricted guidance can omit a baseline choice forever. -/
theorem unrestricted_guidance_can_starve :
    let guided : Nat → Bool := fun _ => false
    let baseline : Nat → Bool := fun index => index = 0
    (∃ index, baseline index = true) ∧
      ¬ ∃ tick, guided tick = true := by
  dsimp
  constructor
  · exact ⟨0, rfl⟩
  · simp

end FairFallback

/-! ## Exact break-even boundary -/

namespace Cost

variable {K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Guidance pays off exactly when its overhead is smaller than the expansion
work it avoids.  The theorem is algebraic and does not assume a particular
runtime cost unit. -/
theorem guided_better_iff
    (guidanceOverhead expansionCost baselineExpansions guidedExpansions : K) :
    guidanceOverhead + guidedExpansions * expansionCost <
        baselineExpansions * expansionCost ↔
      guidanceOverhead <
        (baselineExpansions - guidedExpansions) * expansionCost := by
  rw [sub_mul]
  rw [lt_sub_iff_add_lt]

/-- If guidance avoids no expansions, nonnegative overhead cannot improve the
run. -/
theorem no_saved_expansions_no_speedup
    (guidanceOverhead expansionCost baselineExpansions guidedExpansions : K)
    (overhead_nonnegative : 0 ≤ guidanceOverhead)
    (expansion_nonnegative : 0 ≤ expansionCost)
    (saves_none : baselineExpansions ≤ guidedExpansions) :
    ¬ guidanceOverhead + guidedExpansions * expansionCost <
      baselineExpansions * expansionCost := by
  intro claimed
  have expansion_work_le :
      baselineExpansions * expansionCost ≤
        guidedExpansions * expansionCost :=
    mul_le_mul_of_nonneg_right saves_none expansion_nonnegative
  have total_ge :
      baselineExpansions * expansionCost ≤
        guidanceOverhead + guidedExpansions * expansionCost := by
    have overhead_add :
        guidedExpansions * expansionCost ≤
          guidanceOverhead + guidedExpansions * expansionCost := by
      simpa [add_comm] using
        (add_le_add_right overhead_nonnegative
          (guidedExpansions * expansionCost))
    calc
      baselineExpansions * expansionCost ≤
          guidedExpansions * expansionCost := expansion_work_le
      _ ≤ guidanceOverhead + guidedExpansions * expansionCost := overhead_add
  exact (not_lt_of_ge total_ge) claimed

/-- Positive break-even witness: ten units of guidance are repaid by ten
avoided expansions costing two units each. -/
example : (10 : ℤ) + 10 * 2 < 20 * 2 := by norm_num

/-- Negative break-even witness: the same guidance overhead loses when only
two expansions are avoided. -/
example : ¬ ((10 : ℤ) + 18 * 2 < 20 * 2) := by norm_num

end Cost

end Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization
