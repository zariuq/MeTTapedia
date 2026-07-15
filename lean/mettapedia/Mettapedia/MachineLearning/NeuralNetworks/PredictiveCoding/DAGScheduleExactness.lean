import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ModuleScheduleExactness

/-!
# Scheduled exactness on shared-latent DAGs

This file characterizes when a synchronous reverse-error schedule has received
every parent contribution needed at a shared latent.  The aggregation is over
edge occurrences, so repeated slots and shared branches preserve their full
multiplicity.

For arbitrary signed or zero contributions, scheduled aggregation equals full
reverse aggregation exactly when the omitted contributions sum to zero.  It
therefore characterizes edge-counting admissibility precisely when omitted
contributions cannot cancel.  Strict positivity is one sufficient special
case.  Under exact first-arrival processing and positive active contributions,
exactness is equivalent to all edges leaving each node targeting the same
rank.  This condition is strictly weaker than unit levelization: uniform long
skips are exact, whereas a residual skip whose outgoing branches target
different ranks is not.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

section Schedule

variable {Node Edge : Type*} [Fintype Node] [Fintype Edge] [DecidableEq Node]

/-- Reverse-error contribution transported through one parent edge. -/
noncomputable def dagParentContribution
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ) (e : Edge) : ℝ :=
  G.gain e * parentError (G.target e)

/-- Full reverse aggregation at a shared node. -/
noncomputable def dagFullParentAggregate
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ) (v : Node) : ℝ :=
  ∑ e : Edge, if G.source e = v then dagParentContribution G parentError e else 0

/-- Reverse aggregation containing exactly the contributions that have
arrived by `time`. -/
noncomputable def dagScheduledParentAggregate
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) : ℝ :=
  ∑ e : Edge,
    if G.source e = v then
      if arrival e ≤ time then dagParentContribution G parentError e else 0
    else 0

/-- Reverse contributions still absent at `time`. -/
noncomputable def dagMissedParentAggregate
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) : ℝ :=
  ∑ e : Edge,
    if G.source e = v then
      if arrival e ≤ time then 0 else dagParentContribution G parentError e
    else 0

/-- Every parent-edge contribution at `v` has arrived by `time`. -/
def dagScheduleAdmissible
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) : Prop :=
  ∀ e, G.source e = v → arrival e ≤ time

theorem dagScheduled_add_missed_eq_full
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) :
    dagScheduledParentAggregate G parentError arrival time v +
        dagMissedParentAggregate G parentError arrival time v =
      dagFullParentAggregate G parentError v := by
  classical
  unfold dagScheduledParentAggregate dagMissedParentAggregate dagFullParentAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hs : G.source e = v
  · by_cases ha : arrival e ≤ time <;> simp [hs, ha]
  · simp [hs]

/-- For arbitrary signed or zero edge contributions, scheduled aggregation is
exact precisely when the total omitted contribution vanishes. -/
theorem dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) :
    dagScheduledParentAggregate G parentError arrival time v =
        dagFullParentAggregate G parentError v ↔
      dagMissedParentAggregate G parentError arrival time v = 0 := by
  have hsum := dagScheduled_add_missed_eq_full G parentError arrival time v
  constructor <;> intro h <;> linarith

theorem dagMissedParentAggregate_eq_zero_of_admissible
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node)
    (hadmissible : dagScheduleAdmissible G arrival time v) :
    dagMissedParentAggregate G parentError arrival time v = 0 := by
  classical
  unfold dagMissedParentAggregate
  apply Finset.sum_eq_zero
  intro e _he
  by_cases hs : G.source e = v
  · simp [hs, hadmissible e hs]
  · simp [hs]

/-- An inadmissible schedule whose omitted signed/zero contributions cancel
exactly. -/
def dagMissedContributionsCancel
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) : Prop :=
  ¬ dagScheduleAdmissible G arrival time v ∧
    dagMissedParentAggregate G parentError arrival time v = 0

/-- No-cancellation at a fixed node and time means that a zero omitted sum
certifies that every outgoing edge has in fact arrived. -/
def dagScheduleHasNoMissedCancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) : Prop :=
  dagMissedParentAggregate G parentError arrival time v = 0 →
    dagScheduleAdmissible G arrival time v

/-- Complete signed/zero characterization: exactness arises either from an
admissible schedule or from exact cancellation among omitted contributions. -/
theorem dagScheduledParentAggregate_exact_iff_admissible_or_cancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) :
    dagScheduledParentAggregate G parentError arrival time v =
        dagFullParentAggregate G parentError v ↔
      dagScheduleAdmissible G arrival time v ∨
        dagMissedContributionsCancel G parentError arrival time v := by
  constructor
  · intro hexact
    by_cases hadmissible : dagScheduleAdmissible G arrival time v
    · exact Or.inl hadmissible
    · exact Or.inr ⟨hadmissible,
        (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
          G parentError arrival time v).1 hexact⟩
  · rintro (hadmissible | hcancel)
    · exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
        G parentError arrival time v).2
          (dagMissedParentAggregate_eq_zero_of_admissible
            G parentError arrival time v hadmissible)
    · exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
        G parentError arrival time v).2 hcancel.2

/-- Exactness characterizes counting admissibility if and only if the fixed
schedule has no omitted-contribution cancellation.  This is the exact answer
for arbitrary signed and zero linear contributions. -/
theorem dagExactness_iff_admissible_iff_noMissedCancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) :
    (dagScheduledParentAggregate G parentError arrival time v =
          dagFullParentAggregate G parentError v ↔
        dagScheduleAdmissible G arrival time v) ↔
      dagScheduleHasNoMissedCancellation G parentError arrival time v := by
  constructor
  · intro hcharacterizes hmissed
    apply hcharacterizes.mp
    exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival time v).2 hmissed
  · intro hnoCancellation
    constructor
    · intro hexact
      apply hnoCancellation
      exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
        G parentError arrival time v).1 hexact
    · intro hadmissible
      exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
        G parentError arrival time v).2
          (dagMissedParentAggregate_eq_zero_of_admissible
            G parentError arrival time v hadmissible)

/-! ## Global signed-schedule classification -/

/-- A schedule is globally exact when each node is processed at its assigned
time and has then accumulated its full signed parent aggregate. -/
def dagScheduleExactAtEveryNode
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) : Prop :=
  ∀ v,
    dagScheduledParentAggregate G parentError arrival (nodeTime v) v =
      dagFullParentAggregate G parentError v

/-- Every outgoing edge has arrived by the processing time assigned to its
source node. -/
def dagScheduleAdmissibleAtEveryNode
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (nodeTime : Node → ℕ) : Prop :=
  ∀ v, dagScheduleAdmissible G arrival (nodeTime v) v

/-- At every node, a zero missed signed sum certifies that no edge was
actually omitted. -/
def dagScheduleHasNoMissedCancellationAtEveryNode
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) : Prop :=
  ∀ v,
    dagScheduleHasNoMissedCancellation G parentError arrival (nodeTime v) v

/-- Some processed node is inadmissible but its omitted signed contributions
cancel exactly. -/
def dagScheduleHasMissedCancellationAtSomeNode
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) : Prop :=
  ∃ v, dagMissedContributionsCancel G parentError arrival (nodeTime v) v

/-- Exact global missed-sum law for arbitrary signed or zero contributions,
arbitrary edge arrivals, and arbitrary per-node processing times. -/
theorem dagScheduleExactAtEveryNode_iff_all_missed_eq_zero
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) :
    dagScheduleExactAtEveryNode G parentError arrival nodeTime ↔
      ∀ v, dagMissedParentAggregate G parentError arrival (nodeTime v) v = 0 := by
  constructor <;> intro h v
  · exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival (nodeTime v) v).1 (h v)
  · exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival (nodeTime v) v).2 (h v)

/-- Complete global classification: at every node, exactness is explained
either by genuine edge-counting admissibility or by exact cancellation among
the omitted signed/zero contributions. -/
theorem dagScheduleExactAtEveryNode_iff_each_admissible_or_cancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) :
    dagScheduleExactAtEveryNode G parentError arrival nodeTime ↔
      ∀ v,
        dagScheduleAdmissible G arrival (nodeTime v) v ∨
          dagMissedContributionsCancel G parentError arrival (nodeTime v) v := by
  constructor <;> intro h v
  · exact (dagScheduledParentAggregate_exact_iff_admissible_or_cancellation
      G parentError arrival (nodeTime v) v).1 (h v)
  · exact (dagScheduledParentAggregate_exact_iff_admissible_or_cancellation
      G parentError arrival (nodeTime v) v).2 (h v)

/-- An exact global schedule fails edge-counting admissibility exactly when
at least one node is exact only through missed-contribution cancellation. -/
theorem dagSchedule_exact_not_admissible_iff_hasMissedCancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) :
    (dagScheduleExactAtEveryNode G parentError arrival nodeTime ∧
        ¬ dagScheduleAdmissibleAtEveryNode G arrival nodeTime) ↔
      (dagScheduleExactAtEveryNode G parentError arrival nodeTime ∧
        dagScheduleHasMissedCancellationAtSomeNode
          G parentError arrival nodeTime) := by
  constructor
  · rintro ⟨hexact, hnotAdmissible⟩
    refine ⟨hexact, ?_⟩
    rw [dagScheduleAdmissibleAtEveryNode] at hnotAdmissible
    push Not at hnotAdmissible
    obtain ⟨v, hv⟩ := hnotAdmissible
    refine ⟨v, hv, ?_⟩
    exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival (nodeTime v) v).1 (hexact v)
  · rintro ⟨hexact, v, hv⟩
    refine ⟨hexact, ?_⟩
    intro hadmissible
    exact hv.1 (hadmissible v)

/-- Exactness characterizes admissibility at every individual node exactly
when the entire signed schedule has no missed cancellation. -/
theorem dagSchedule_pointwiseExactness_iff_admissible_iff_noCancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ) :
    (∀ v,
      (dagScheduledParentAggregate G parentError arrival (nodeTime v) v =
          dagFullParentAggregate G parentError v ↔
        dagScheduleAdmissible G arrival (nodeTime v) v)) ↔
      dagScheduleHasNoMissedCancellationAtEveryNode
        G parentError arrival nodeTime := by
  unfold dagScheduleHasNoMissedCancellationAtEveryNode
  constructor <;> intro h v
  · exact (dagExactness_iff_admissible_iff_noMissedCancellation
      G parentError arrival (nodeTime v) v).1 (h v)
  · exact (dagExactness_iff_admissible_iff_noMissedCancellation
      G parentError arrival (nodeTime v) v).2 (h v)

/-- In the no-cancellation regime, global numerical exactness and global
edge-counting admissibility coincide. -/
theorem dagScheduleExactAtEveryNode_iff_admissible_of_noCancellation
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (nodeTime : Node → ℕ)
    (hnoCancellation : dagScheduleHasNoMissedCancellationAtEveryNode
      G parentError arrival nodeTime) :
    dagScheduleExactAtEveryNode G parentError arrival nodeTime ↔
      dagScheduleAdmissibleAtEveryNode G arrival nodeTime := by
  constructor <;> intro h v
  · exact hnoCancellation v
      ((dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
        G parentError arrival (nodeTime v) v).1 (h v))
  · exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival (nodeTime v) v).2
        (dagMissedParentAggregate_eq_zero_of_admissible
          G parentError arrival (nodeTime v) v (h v))

/-! ## Value-independent structural cancellation -/

/-- Total gain of the missed outgoing edges from `v` that target one fixed
node.  These are the coefficients of the missed aggregate as a linear
functional of the parent-error assignment. -/
noncomputable def dagMissedTargetGain
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (v target : Node) : ℝ :=
  ∑ e : Edge,
    if G.source e = v ∧ time < arrival e ∧ G.target e = target then
      G.gain e
    else 0

/-- Regroup the missed signed aggregate by target node. -/
theorem dagMissedParentAggregate_eq_sum_targetGain
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node) :
    dagMissedParentAggregate G parentError arrival time v =
      ∑ target : Node,
        dagMissedTargetGain G arrival time v target * parentError target := by
  classical
  unfold dagMissedParentAggregate dagMissedTargetGain dagParentContribution
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hs : G.source e = v
  · by_cases ha : arrival e ≤ time
    · simp [hs, ha, not_lt_of_ge ha]
    · have hlt : time < arrival e := Nat.lt_of_not_ge ha
      simp [hs, ha, hlt]
  · simp [hs]

/-- A schedule is structurally exact at a node when it is numerically exact
for every possible parent-error assignment, rather than through an accidental
cancellation at one chosen assignment. -/
def dagScheduleUniversallyExactAtNode
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) : Prop :=
  ∀ parentError : Node → ℝ,
    dagScheduledParentAggregate G parentError arrival time v =
      dagFullParentAggregate G parentError v

/-- Exact value-independent structural criterion: universal numerical
exactness holds precisely when every missed target-group gain vanishes. -/
theorem dagScheduleUniversallyExactAtNode_iff_targetGain_zero
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) :
    dagScheduleUniversallyExactAtNode G arrival time v ↔
      ∀ target, dagMissedTargetGain G arrival time v target = 0 := by
  constructor
  · intro huniversal target
    have hexact := huniversal (fun u => if u = target then 1 else 0)
    have hmissed := (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G (fun u => if u = target then 1 else 0) arrival time v).1 hexact
    rw [dagMissedParentAggregate_eq_sum_targetGain] at hmissed
    simpa using hmissed
  · intro hcoeff parentError
    apply (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival time v).2
    rw [dagMissedParentAggregate_eq_sum_targetGain]
    simp [hcoeff]

/-- At a node, no two distinct outgoing edge occurrences target the same
node. -/
def OutgoingTargetsInjectiveAt
    (G : SharedLatentDAG Node Edge) (v : Node) : Prop :=
  ∀ e₁ e₂, G.source e₁ = v → G.source e₂ = v →
    G.target e₁ = G.target e₂ → e₁ = e₂

/-- With target-injective outgoing slots and nonzero gains, structural
exactness cannot hide a missed edge and is equivalent to admissibility. -/
theorem dagScheduleUniversallyExactAtNode_iff_admissible_of_targetInjective
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node)
    (hinjective : OutgoingTargetsInjectiveAt G v)
    (hgain : ∀ e, G.source e = v → G.gain e ≠ 0) :
    dagScheduleUniversallyExactAtNode G arrival time v ↔
      dagScheduleAdmissible G arrival time v := by
  constructor
  · intro huniversal e hs
    have hcoeff :=
      (dagScheduleUniversallyExactAtNode_iff_targetGain_zero
        G arrival time v).1 huniversal (G.target e)
    by_contra hnot
    have hlt : time < arrival e := Nat.lt_of_not_ge hnot
    have hsingle :
        dagMissedTargetGain G arrival time v (G.target e) = G.gain e := by
      classical
      unfold dagMissedTargetGain
      rw [Finset.sum_eq_single e]
      · simp [hs, hlt]
      · intro j _hj hjne
        by_cases hj :
            G.source j = v ∧ time < arrival j ∧ G.target j = G.target e
        · exact False.elim (hjne (hinjective j e hj.1 hs hj.2.2))
        · simp [hj]
      · simp
    rw [hsingle] at hcoeff
    exact hgain e hs hcoeff
  · intro hadmissible parentError
    exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
      G parentError arrival time v).2
        (dagMissedParentAggregate_eq_zero_of_admissible
          G parentError arrival time v hadmissible)

/-- All outgoing gains at `v` share a strict sign exactly when one scalar
orientation makes every active contribution positive. -/
def HasCommonOutgoingGainSignAt
    (G : SharedLatentDAG Node Edge) (v : Node) : Prop :=
  ∃ scale : ℝ, ∀ e, G.source e = v → 0 < G.gain e * scale

/-- Global structural exactness quantifies over every parent-error assignment
and every scheduled node. -/
def dagScheduleUniversallyExactAtEveryNode
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (nodeTime : Node → ℕ) : Prop :=
  ∀ parentError,
    dagScheduleExactAtEveryNode G parentError arrival nodeTime

theorem dagScheduleUniversallyExactAtEveryNode_iff_targetGain_zero
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (nodeTime : Node → ℕ) :
    dagScheduleUniversallyExactAtEveryNode G arrival nodeTime ↔
      ∀ v target,
        dagMissedTargetGain G arrival (nodeTime v) v target = 0 := by
  constructor
  · intro huniversal v
    exact (dagScheduleUniversallyExactAtNode_iff_targetGain_zero
      G arrival (nodeTime v) v).1 (fun parentError => huniversal parentError v)
  · intro hcoeff parentError v
    exact (dagScheduleUniversallyExactAtNode_iff_targetGain_zero
      G arrival (nodeTime v) v).2 (hcoeff v) parentError

theorem dagScheduledParentAggregate_eq_full_of_admissible
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node)
    (hadmissible : dagScheduleAdmissible G arrival time v) :
    dagScheduledParentAggregate G parentError arrival time v =
      dagFullParentAggregate G parentError v := by
  classical
  unfold dagScheduledParentAggregate dagFullParentAggregate
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hs : G.source e = v
  · simp [hs, hadmissible e hs]
  · simp [hs]

/-- With positive active contributions, equality with full reverse
aggregation characterizes schedule admissibility rather than merely following
from it. -/
theorem dagScheduledParentAggregate_eq_full_iff_admissible
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (arrival : Edge → ℕ) (time : ℕ) (v : Node)
    (hpositive : ∀ e, G.source e = v → 0 < dagParentContribution G parentError e) :
    dagScheduledParentAggregate G parentError arrival time v =
        dagFullParentAggregate G parentError v ↔
      dagScheduleAdmissible G arrival time v := by
  constructor
  · intro hequal e hs
    by_contra hnot
    have hmissed :
        0 < dagMissedParentAggregate G parentError arrival time v := by
      unfold dagMissedParentAggregate
      apply Finset.sum_pos'
      · intro j _hj
        by_cases hsj : G.source j = v
        · by_cases haj : arrival j ≤ time
          · simp [hsj, haj]
          · simpa [hsj, haj] using (hpositive j hsj).le
        · simp [hsj]
      · refine ⟨e, Finset.mem_univ e, ?_⟩
        simp [hs, hnot, hpositive e hs]
    have hsum := dagScheduled_add_missed_eq_full G parentError arrival time v
    rw [hequal] at hsum
    linarith
  · exact dagScheduledParentAggregate_eq_full_of_admissible
      G parentError arrival time v

/-- Common-sign gains rule out structural cancellation, so universal
exactness and admissibility coincide. -/
theorem dagScheduleUniversallyExactAtNode_iff_admissible_of_commonSign
    (G : SharedLatentDAG Node Edge) (arrival : Edge → ℕ)
    (time : ℕ) (v : Node) (hcommon : HasCommonOutgoingGainSignAt G v) :
    dagScheduleUniversallyExactAtNode G arrival time v ↔
      dagScheduleAdmissible G arrival time v := by
  obtain ⟨scale, hscale⟩ := hcommon
  constructor
  · intro huniversal
    have hexact := huniversal (fun _ => scale)
    exact (dagScheduledParentAggregate_eq_full_iff_admissible
      G (fun _ => scale) arrival time v (by
        intro e hs
        simpa [dagParentContribution] using hscale e hs)).1 hexact
  · intro hadmissible parentError
    exact dagScheduledParentAggregate_eq_full_of_admissible
      G parentError arrival time v hadmissible

/-! ## Unit-levelized arrival threshold -/

/-- Every graph edge advances exactly one level.  Longer skip branches must
therefore be represented by explicit intermediate nodes. -/
def IsUnitLevelized (G : SharedLatentDAG Node Edge) : Prop :=
  ∀ e, G.rank (G.target e) = G.rank (G.source e) + 1

/-- Reverse-error arrival time at an edge's target level. -/
def dagEdgeErrorArrival
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) (e : Edge) : ℕ :=
  headRank - G.rank (G.target e)

/-- Common reverse-error arrival time of edges leaving a unit-levelized node. -/
def dagNodeErrorArrival
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) (v : Node) : ℕ :=
  headRank - (G.rank v + 1)

omit [DecidableEq Node] in
theorem dagEdgeErrorArrival_eq_nodeErrorArrival
    (G : SharedLatentDAG Node Edge) (headRank : ℕ)
    (hlevelized : IsUnitLevelized G)
    (e : Edge) (v : Node) (hsource : G.source e = v) :
    dagEdgeErrorArrival G headRank e = dagNodeErrorArrival G headRank v := by
  unfold dagEdgeErrorArrival dagNodeErrorArrival
  rw [hlevelized e, hsource]

omit [DecidableEq Node] in
theorem dagScheduleAdmissible_iff_level_threshold
    (G : SharedLatentDAG Node Edge) (headRank time : ℕ) (v : Node)
    (hlevelized : IsUnitLevelized G)
    (houtgoing : ∃ e, G.source e = v) :
    dagScheduleAdmissible G (dagEdgeErrorArrival G headRank) time v ↔
      dagNodeErrorArrival G headRank v ≤ time := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := houtgoing
    rw [← dagEdgeErrorArrival_eq_nodeErrorArrival G headRank hlevelized e v he]
    exact h e he
  · intro h e he
    rw [dagEdgeErrorArrival_eq_nodeErrorArrival G headRank hlevelized e v he]
    exact h

/-- Exact admissible-schedule characterization for a unit-levelized shared
DAG. -/
theorem levelizedDAG_scheduledParentAggregate_exact_iff
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (headRank time : ℕ) (v : Node)
    (hlevelized : IsUnitLevelized G)
    (houtgoing : ∃ e, G.source e = v)
    (hpositive : ∀ e, G.source e = v → 0 < dagParentContribution G parentError e) :
    dagScheduledParentAggregate G parentError (dagEdgeErrorArrival G headRank) time v =
        dagFullParentAggregate G parentError v ↔
      dagNodeErrorArrival G headRank v ≤ time := by
  calc
    _ ↔ dagScheduleAdmissible G (dagEdgeErrorArrival G headRank) time v :=
      dagScheduledParentAggregate_eq_full_iff_admissible
        G parentError (dagEdgeErrorArrival G headRank) time v hpositive
    _ ↔ _ := dagScheduleAdmissible_iff_level_threshold
      G headRank time v hlevelized houtgoing

/-! ## Exact first-arrival schedules on arbitrary finite DAGs -/

/-- Arrival times realized by the outgoing edges of a node. -/
def dagOutgoingArrivalSet
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) (v : Node) : Set ℕ :=
  {time | ∃ e, G.source e = v ∧ dagEdgeErrorArrival G headRank e = time}

/-- The first reverse-error arrival at a node.  It is relevant only when the
node has an outgoing edge; the empty-set value is harmless. -/
noncomputable def dagFirstErrorArrival
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) (v : Node) : ℕ :=
  sInf (dagOutgoingArrivalSet G headRank v)

omit [DecidableEq Node] in
theorem dagFirstErrorArrival_is_realized
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) (v : Node)
    (houtgoing : ∃ e, G.source e = v) :
    ∃ e, G.source e = v ∧
      dagEdgeErrorArrival G headRank e = dagFirstErrorArrival G headRank v := by
  have hnonempty : (dagOutgoingArrivalSet G headRank v).Nonempty := by
    obtain ⟨e, he⟩ := houtgoing
    exact ⟨dagEdgeErrorArrival G headRank e, e, he, rfl⟩
  exact Nat.sInf_mem hnonempty

omit [DecidableEq Node] in
theorem dagFirstErrorArrival_le
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) (v : Node)
    (e : Edge) (hsource : G.source e = v) :
    dagFirstErrorArrival G headRank v ≤ dagEdgeErrorArrival G headRank e := by
  exact Nat.sInf_le ⟨e, hsource, rfl⟩

/-- Every pair of outgoing edges from a node has the same reverse arrival. -/
def HasUniformOutgoingArrivals
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) : Prop :=
  ∀ v e₁ e₂, G.source e₁ = v → G.source e₂ = v →
    dagEdgeErrorArrival G headRank e₁ = dagEdgeErrorArrival G headRank e₂

/-- Every pair of outgoing edges from a node targets the same graph rank. -/
def HasUniformOutgoingTargetRanks (G : SharedLatentDAG Node Edge) : Prop :=
  ∀ v e₁ e₂, G.source e₁ = v → G.source e₂ = v →
    G.rank (G.target e₁) = G.rank (G.target e₂)

/-- Global first-arrival exactness: every node is processed when its first
outgoing reverse contribution arrives, and every such aggregate is exact. -/
def dagFirstArrivalScheduleExact
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (headRank : ℕ) : Prop :=
  ∀ v,
    dagScheduledParentAggregate G parentError
        (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v =
      dagFullParentAggregate G parentError v

/-- A first-arrival schedule is structurally exact when it is exact for every
possible parent-error assignment. -/
def dagFirstArrivalScheduleUniversallyExact
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) : Prop :=
  ∀ parentError, dagFirstArrivalScheduleExact G parentError headRank

/-- Exact structural criterion for first-arrival processing: at every source,
the total gain of each missed target group must vanish. -/
theorem dagFirstArrivalScheduleUniversallyExact_iff_targetGain_zero
    (G : SharedLatentDAG Node Edge) (headRank : ℕ) :
    dagFirstArrivalScheduleUniversallyExact G headRank ↔
      ∀ v target,
        dagMissedTargetGain G (dagEdgeErrorArrival G headRank)
          (dagFirstErrorArrival G headRank v) v target = 0 := by
  constructor
  · intro huniversal v
    exact (dagScheduleUniversallyExactAtNode_iff_targetGain_zero G
      (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v).1
        (fun parentError => huniversal parentError v)
  · intro hcoeff parentError v
    exact (dagScheduleUniversallyExactAtNode_iff_targetGain_zero G
      (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v).2
        (hcoeff v) parentError

omit [DecidableEq Node] in
theorem uniformOutgoingArrivals_firstArrival_admissible
    (G : SharedLatentDAG Node Edge) (headRank : ℕ)
    (huniform : HasUniformOutgoingArrivals G headRank) (v : Node) :
    dagScheduleAdmissible G (dagEdgeErrorArrival G headRank)
      (dagFirstErrorArrival G headRank v) v := by
  intro e he
  obtain ⟨firstEdge, hfirstSource, hfirstArrival⟩ :=
    dagFirstErrorArrival_is_realized G headRank v ⟨e, he⟩
  rw [← hfirstArrival]
  exact le_of_eq (huniform v e firstEdge he hfirstSource)

/-- Exact existence characterization under first-arrival semantics.  With
positive active contributions, a finite DAG has an exact first-arrival
schedule exactly when each node's outgoing edges arrive simultaneously. -/
theorem dagFirstArrivalScheduleExact_iff_uniformOutgoingArrivals
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (headRank : ℕ)
    (hpositive : ∀ e, 0 < dagParentContribution G parentError e) :
    dagFirstArrivalScheduleExact G parentError headRank ↔
      HasUniformOutgoingArrivals G headRank := by
  constructor
  · intro hexact v e₁ e₂ he₁ he₂
    have hadmissible : dagScheduleAdmissible G (dagEdgeErrorArrival G headRank)
        (dagFirstErrorArrival G headRank v) v :=
      (dagScheduledParentAggregate_eq_full_iff_admissible G parentError
        (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v
        (fun e _ => hpositive e)).mp (hexact v)
    have hle₁ := dagFirstErrorArrival_le G headRank v e₁ he₁
    have hle₂ := dagFirstErrorArrival_le G headRank v e₂ he₂
    have hge₁ := hadmissible e₁ he₁
    have hge₂ := hadmissible e₂ he₂
    omega
  · intro huniform v
    exact dagScheduledParentAggregate_eq_full_of_admissible G parentError
      (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v
      (uniformOutgoingArrivals_firstArrival_admissible G headRank huniform v)

/-- In a common-sign graph, structural first-arrival exactness is equivalent
to simultaneous outgoing arrivals at every source. -/
theorem dagFirstArrivalScheduleUniversallyExact_iff_uniformOutgoingArrivals_of_commonSign
    (G : SharedLatentDAG Node Edge) (headRank : ℕ)
    (hcommon : ∀ v, HasCommonOutgoingGainSignAt G v) :
    dagFirstArrivalScheduleUniversallyExact G headRank ↔
      HasUniformOutgoingArrivals G headRank := by
  constructor
  · intro huniversal v e₁ e₂ he₁ he₂
    have hadmissible :
        dagScheduleAdmissible G (dagEdgeErrorArrival G headRank)
          (dagFirstErrorArrival G headRank v) v :=
      (dagScheduleUniversallyExactAtNode_iff_admissible_of_commonSign G
        (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v
        (hcommon v)).1 (fun parentError => huniversal parentError v)
    have hle₁ := dagFirstErrorArrival_le G headRank v e₁ he₁
    have hle₂ := dagFirstErrorArrival_le G headRank v e₂ he₂
    have hge₁ := hadmissible e₁ he₁
    have hge₂ := hadmissible e₂ he₂
    omega
  · intro huniform parentError v
    exact dagScheduledParentAggregate_eq_full_of_admissible G parentError
      (dagEdgeErrorArrival G headRank) (dagFirstErrorArrival G headRank v) v
      (uniformOutgoingArrivals_firstArrival_admissible G headRank huniform v)

omit [DecidableEq Node] in
theorem uniformOutgoingTargetRanks_iff_uniformOutgoingArrivals
    (G : SharedLatentDAG Node Edge) (headRank : ℕ)
    (hhead : ∀ n, G.rank n ≤ headRank) :
    HasUniformOutgoingTargetRanks G ↔ HasUniformOutgoingArrivals G headRank := by
  constructor
  · intro huniform v e₁ e₂ he₁ he₂
    unfold dagEdgeErrorArrival
    rw [huniform v e₁ e₂ he₁ he₂]
  · intro huniform v e₁ e₂ he₁ he₂
    have harrival := huniform v e₁ e₂ he₁ he₂
    unfold dagEdgeErrorArrival at harrival
    have h₁ := hhead (G.target e₁)
    have h₂ := hhead (G.target e₂)
    omega

/-- Under a valid head-rank bound, the common-sign structural criterion can
equivalently be stated as uniform outgoing target rank. -/
theorem dagFirstArrivalScheduleUniversallyExact_iff_uniformOutgoingTargetRanks_of_commonSign
    (G : SharedLatentDAG Node Edge) (headRank : ℕ)
    (hhead : ∀ n, G.rank n ≤ headRank)
    (hcommon : ∀ v, HasCommonOutgoingGainSignAt G v) :
    dagFirstArrivalScheduleUniversallyExact G headRank ↔
      HasUniformOutgoingTargetRanks G := by
  rw [dagFirstArrivalScheduleUniversallyExact_iff_uniformOutgoingArrivals_of_commonSign
    G headRank hcommon]
  exact (uniformOutgoingTargetRanks_iff_uniformOutgoingArrivals
    G headRank hhead).symm

omit [DecidableEq Node] in
theorem unitLevelized_hasUniformOutgoingTargetRanks
    (G : SharedLatentDAG Node Edge) (hlevelized : IsUnitLevelized G) :
    HasUniformOutgoingTargetRanks G := by
  intro v e₁ e₂ he₁ he₂
  rw [hlevelized e₁, hlevelized e₂, he₁, he₂]

/-- Structural crown: when `headRank` bounds graph ranks, the true class of
exact first-arrival DAGs is uniform outgoing target rank, strictly weaker
than unit levelization. -/
theorem dagFirstArrivalScheduleExact_iff_uniformOutgoingTargetRanks
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (headRank : ℕ) (hhead : ∀ n, G.rank n ≤ headRank)
    (hpositive : ∀ e, 0 < dagParentContribution G parentError e) :
    dagFirstArrivalScheduleExact G parentError headRank ↔
      HasUniformOutgoingTargetRanks G := by
  rw [dagFirstArrivalScheduleExact_iff_uniformOutgoingArrivals
    G parentError headRank hpositive]
  exact (uniformOutgoingTargetRanks_iff_uniformOutgoingArrivals
    G headRank hhead).symm

/-- Unit levelization remains a sufficient special case of exact
first-arrival processing. -/
theorem unitLevelized_firstArrivalScheduleExact
    (G : SharedLatentDAG Node Edge) (parentError : Node → ℝ)
    (headRank : ℕ) (hhead : ∀ n, G.rank n ≤ headRank)
    (hpositive : ∀ e, 0 < dagParentContribution G parentError e)
    (hlevelized : IsUnitLevelized G) :
    dagFirstArrivalScheduleExact G parentError headRank := by
  exact (dagFirstArrivalScheduleExact_iff_uniformOutgoingTargetRanks
    G parentError headRank hhead hpositive).2
      (unitLevelized_hasUniformOutgoingTargetRanks G hlevelized)

end Schedule

/-! ## Levelized-skip and residual-skip fixtures -/

/-- A levelized diamond.  Node `0` is shared by two branches; the second
branch is a skip arm made unit-levelized by the explicit adapter node `2`.
Both branches join at node `3`. -/
noncomputable def levelizedSkipDiamondGraph : SharedLatentDAG (Fin 4) (Fin 4) where
  source := fun e => if e.val < 2 then 0 else if e.val = 2 then 1 else 2
  target := fun e => if e.val = 0 then 1 else if e.val = 1 then 2 else 3
  rank := fun n => if n.val = 0 then 0 else if n.val = 3 then 2 else 1
  forward := by
    intro e
    fin_cases e <;> norm_num
  gain := fun _ => 1
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {3}

noncomputable def levelizedSkipDiamondParentError : Fin 4 → ℝ :=
  fun n => if n.val = 1 ∨ n.val = 2 then 1 else 0

theorem levelizedSkipDiamondGraph_isUnitLevelized :
    IsUnitLevelized levelizedSkipDiamondGraph := by
  intro e
  fin_cases e <;> simp [levelizedSkipDiamondGraph]

theorem levelizedSkipDiamond_source_has_two_positive_contributions
    (e : Fin 4) (hsource : levelizedSkipDiamondGraph.source e = 0) :
    0 < dagParentContribution levelizedSkipDiamondGraph
      levelizedSkipDiamondParentError e := by
  fin_cases e <;>
    simp [levelizedSkipDiamondGraph, levelizedSkipDiamondParentError,
      dagParentContribution] at hsource ⊢

theorem levelizedSkipDiamond_source_has_outgoing_edge :
    ∃ e, levelizedSkipDiamondGraph.source e = 0 := by
  exact ⟨0, by norm_num [levelizedSkipDiamondGraph]⟩

/-- Once the common level-one arrival has occurred, the scheduled reverse
aggregate at the shared source equals the full two-branch aggregate. -/
theorem levelizedSkipDiamond_admissibleSchedule_positive_example :
    dagScheduledParentAggregate levelizedSkipDiamondGraph
        levelizedSkipDiamondParentError
        (dagEdgeErrorArrival levelizedSkipDiamondGraph 2) 1 0 =
      dagFullParentAggregate levelizedSkipDiamondGraph
        levelizedSkipDiamondParentError 0 := by
  exact (levelizedDAG_scheduledParentAggregate_exact_iff
    levelizedSkipDiamondGraph levelizedSkipDiamondParentError 2 1 0
    levelizedSkipDiamondGraph_isUnitLevelized
    levelizedSkipDiamond_source_has_outgoing_edge
    levelizedSkipDiamond_source_has_two_positive_contributions).2 (by
      simp [dagNodeErrorArrival, levelizedSkipDiamondGraph])

theorem levelizedSkipDiamond_fullAggregate_value :
    dagFullParentAggregate levelizedSkipDiamondGraph
      levelizedSkipDiamondParentError 0 = 2 := by
  norm_num [dagFullParentAggregate, dagParentContribution,
    levelizedSkipDiamondGraph, levelizedSkipDiamondParentError,
    Fin.sum_univ_succ]

/-- Before the common arrival time, neither branch contribution is present. -/
theorem levelizedSkipDiamond_prematureSchedule_negative_example :
    dagScheduledParentAggregate levelizedSkipDiamondGraph
        levelizedSkipDiamondParentError
        (dagEdgeErrorArrival levelizedSkipDiamondGraph 2) 0 0 ≠
      dagFullParentAggregate levelizedSkipDiamondGraph
        levelizedSkipDiamondParentError 0 := by
  intro hequal
  have hthreshold := (levelizedDAG_scheduledParentAggregate_exact_iff
    levelizedSkipDiamondGraph levelizedSkipDiamondParentError 2 0 0
    levelizedSkipDiamondGraph_isUnitLevelized
    levelizedSkipDiamond_source_has_outgoing_edge
    levelizedSkipDiamond_source_has_two_positive_contributions).1 hequal
  simp [dagNodeErrorArrival, levelizedSkipDiamondGraph] at hthreshold

/-! A uniform long skip refutes necessity of unit levelization. -/

/-- Both outgoing edges skip directly from rank zero to rank three. -/
noncomputable def uniformLongSkipGraph : SharedLatentDAG (Fin 3) (Fin 2) where
  source := fun _ => 0
  target := fun _ => 2
  rank := fun n => if n.val = 0 then 0 else if n.val = 1 then 1 else 3
  forward := by
    intro e
    fin_cases e <;> norm_num
  gain := fun _ => 1
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {2}

noncomputable def uniformLongSkipParentError : Fin 3 → ℝ := fun _ => 1

theorem uniformLongSkipGraph_not_unitLevelized :
    ¬ IsUnitLevelized uniformLongSkipGraph := by
  intro hlevelized
  have hedge := hlevelized 0
  simp [uniformLongSkipGraph] at hedge

theorem uniformLongSkipGraph_hasUniformOutgoingTargetRanks :
    HasUniformOutgoingTargetRanks uniformLongSkipGraph := by
  intro v e₁ e₂ he₁ he₂
  simp [uniformLongSkipGraph]

theorem uniformLongSkipGraph_rank_le_four (n : Fin 3) :
    uniformLongSkipGraph.rank n ≤ 4 := by
  fin_cases n <;> norm_num [uniformLongSkipGraph]

theorem uniformLongSkipGraph_positive_contributions (e : Fin 2) :
    0 < dagParentContribution uniformLongSkipGraph
      uniformLongSkipParentError e := by
  fin_cases e <;>
    norm_num [dagParentContribution, uniformLongSkipGraph,
      uniformLongSkipParentError]

/-- Positive counterexample to necessity: a non-unit-levelized graph can
still be exact when every outgoing branch makes the same long skip. -/
theorem uniformLongSkipGraph_firstArrival_exact :
    dagFirstArrivalScheduleExact uniformLongSkipGraph
      uniformLongSkipParentError 4 := by
  exact (dagFirstArrivalScheduleExact_iff_uniformOutgoingTargetRanks
    uniformLongSkipGraph uniformLongSkipParentError 4
    uniformLongSkipGraph_rank_le_four
    uniformLongSkipGraph_positive_contributions).2
      uniformLongSkipGraph_hasUniformOutgoingTargetRanks

/-- Unlevelized residual shape: edge `0` is a one-step skip contribution at
rank three, while edge `1` starts the long branch at rank one. -/
noncomputable def unlevelizedResidualSkipGraph : SharedLatentDAG (Fin 3) (Fin 2) where
  source := fun _ => 0
  target := fun e => if e.val = 0 then 2 else 1
  rank := fun n => if n.val = 0 then 0 else if n.val = 1 then 1 else 3
  forward := by
    intro e
    fin_cases e <;> norm_num
  gain := fun _ => 1
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {2}

noncomputable def unlevelizedResidualSkipParentError : Fin 3 → ℝ :=
  fun n => if n.val = 0 then 0 else 1

theorem unlevelizedResidualSkipGraph_not_unitLevelized :
    ¬ IsUnitLevelized unlevelizedResidualSkipGraph := by
  intro hlevelized
  have hedge := hlevelized 0
  simp [unlevelizedResidualSkipGraph] at hedge

theorem unlevelizedResidualSkip_arrival_times :
    dagEdgeErrorArrival unlevelizedResidualSkipGraph 4 0 = 1 ∧
      dagEdgeErrorArrival unlevelizedResidualSkipGraph 4 1 = 3 := by
  simp [dagEdgeErrorArrival, unlevelizedResidualSkipGraph]

theorem unlevelizedResidualSkipGraph_not_uniformOutgoingTargetRanks :
    ¬ HasUniformOutgoingTargetRanks unlevelizedResidualSkipGraph := by
  intro huniform
  have h := huniform 0 0 1 (by simp [unlevelizedResidualSkipGraph])
    (by simp [unlevelizedResidualSkipGraph])
  simp [unlevelizedResidualSkipGraph] at h

theorem unlevelizedResidualSkipGraph_rank_le_four (n : Fin 3) :
    unlevelizedResidualSkipGraph.rank n ≤ 4 := by
  fin_cases n <;> norm_num [unlevelizedResidualSkipGraph]

theorem unlevelizedResidualSkipGraph_positive_contributions (e : Fin 2) :
    0 < dagParentContribution unlevelizedResidualSkipGraph
      unlevelizedResidualSkipParentError e := by
  fin_cases e <;>
    norm_num [dagParentContribution, unlevelizedResidualSkipGraph,
      unlevelizedResidualSkipParentError]

/-- The residual skip is outside the exact first-arrival class because its
two outgoing branches target different ranks. -/
theorem unlevelizedResidualSkipGraph_firstArrival_not_exact :
    ¬ dagFirstArrivalScheduleExact unlevelizedResidualSkipGraph
      unlevelizedResidualSkipParentError 4 := by
  rw [dagFirstArrivalScheduleExact_iff_uniformOutgoingTargetRanks
    unlevelizedResidualSkipGraph unlevelizedResidualSkipParentError 4
    unlevelizedResidualSkipGraph_rank_le_four
    unlevelizedResidualSkipGraph_positive_contributions]
  exact unlevelizedResidualSkipGraph_not_uniformOutgoingTargetRanks

/-- At the first arrival, the skip contribution is present but the long-path
contribution is still missing, reproducing the existing residual-skip
boundary numerically. -/
theorem unlevelizedResidualSkip_firstArrival_failure_example :
    dagScheduledParentAggregate unlevelizedResidualSkipGraph
        unlevelizedResidualSkipParentError
        (dagEdgeErrorArrival unlevelizedResidualSkipGraph 4) 1 0 =
        residualSkipNaiveScheduledGainGradient 1 1 1 1 ∧
      dagFullParentAggregate unlevelizedResidualSkipGraph
        unlevelizedResidualSkipParentError 0 =
        residualSkipBackpropGainGradient 1 1 1 ∧
      dagScheduledParentAggregate unlevelizedResidualSkipGraph
          unlevelizedResidualSkipParentError
          (dagEdgeErrorArrival unlevelizedResidualSkipGraph 4) 1 0 ≠
        dagFullParentAggregate unlevelizedResidualSkipGraph
          unlevelizedResidualSkipParentError 0 := by
  simp [dagScheduledParentAggregate, dagFullParentAggregate,
    dagParentContribution, dagEdgeErrorArrival, unlevelizedResidualSkipGraph,
    unlevelizedResidualSkipParentError, residualSkipNaiveScheduledGainGradient,
    residualSkipBackpropGainGradient, Fin.sum_univ_succ]

/-! ## Signed and zero cancellation boundaries -/

/-- Three parallel parent slots with contributions `2`, `1`, and `-1`. -/
noncomputable def signedCancellationGraph : SharedLatentDAG (Fin 2) (Fin 3) where
  source := fun _ => 0
  target := fun _ => 1
  rank := fun n => n.val
  forward := by
    intro e
    fin_cases e <;> norm_num
  gain := fun e => if e.val = 0 then 2 else if e.val = 1 then 1 else -1
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {1}

noncomputable def signedCancellationParentError : Fin 2 → ℝ := fun _ => 1

/-- At time zero only the contribution `2` has arrived; the omitted `1` and
`-1` cancel. -/
def signedCancellationArrival : Fin 3 → ℕ :=
  fun e => if e.val = 0 then 0 else 1

theorem signedCancellation_missedAggregate_zero :
    dagMissedParentAggregate signedCancellationGraph signedCancellationParentError
      signedCancellationArrival 0 0 = 0 := by
  norm_num [dagMissedParentAggregate, dagParentContribution,
    signedCancellationGraph, signedCancellationParentError,
    signedCancellationArrival, Fin.sum_univ_succ]

/-- The cancellation is structural rather than tied to the chosen fixture
values: every missed target-group gain vanishes. -/
theorem signedCancellation_missedTargetGain_zero (target : Fin 2) :
    dagMissedTargetGain signedCancellationGraph signedCancellationArrival
      0 0 target = 0 := by
  fin_cases target <;>
    norm_num [dagMissedTargetGain, signedCancellationGraph,
      signedCancellationArrival, Fin.sum_univ_succ]

/-- Consequently the inadmissible signed schedule is exact for every possible
parent-error assignment. -/
theorem signedCancellation_schedule_universallyExact :
    dagScheduleUniversallyExactAtNode signedCancellationGraph
      signedCancellationArrival 0 0 := by
  exact (dagScheduleUniversallyExactAtNode_iff_targetGain_zero
    signedCancellationGraph signedCancellationArrival 0 0).2
      signedCancellation_missedTargetGain_zero

theorem signedCancellation_schedule_not_admissible :
    ¬ dagScheduleAdmissible signedCancellationGraph signedCancellationArrival 0 0 := by
  intro hadmissible
  have hedge := hadmissible 1 (by norm_num [signedCancellationGraph])
  norm_num [signedCancellationArrival] at hedge

/-- Cancellation makes an edge-counting-inadmissible schedule numerically
exact.  This is the failure boundary that the old positivity hypothesis hid. -/
theorem signedCancellation_inadmissible_but_exact_negative_example :
    ¬ dagScheduleAdmissible signedCancellationGraph signedCancellationArrival 0 0 ∧
      dagScheduledParentAggregate signedCancellationGraph
          signedCancellationParentError signedCancellationArrival 0 0 =
        dagFullParentAggregate signedCancellationGraph
          signedCancellationParentError 0 ∧
      dagMissedContributionsCancel signedCancellationGraph
        signedCancellationParentError signedCancellationArrival 0 0 := by
  refine ⟨signedCancellation_schedule_not_admissible, ?_,
    signedCancellation_schedule_not_admissible,
    signedCancellation_missedAggregate_zero⟩
  exact (dagScheduledParentAggregate_eq_full_iff_missed_eq_zero
    signedCancellationGraph signedCancellationParentError
    signedCancellationArrival 0 0).2 signedCancellation_missedAggregate_zero

/-- Both graph nodes are processed at time zero in the global signed fixture. -/
def signedCancellationNodeTime : Fin 2 → ℕ := fun _ => 0

theorem signedCancellation_globalSchedule_exact :
    dagScheduleExactAtEveryNode signedCancellationGraph
      signedCancellationParentError signedCancellationArrival
      signedCancellationNodeTime := by
  intro v
  fin_cases v
  · exact signedCancellation_inadmissible_but_exact_negative_example.2.1
  · norm_num [dagScheduledParentAggregate, dagFullParentAggregate,
      signedCancellationGraph, signedCancellationNodeTime, Fin.sum_univ_succ]

theorem signedCancellation_globalSchedule_not_admissible :
    ¬ dagScheduleAdmissibleAtEveryNode signedCancellationGraph
      signedCancellationArrival signedCancellationNodeTime := by
  intro hadmissible
  exact signedCancellation_schedule_not_admissible (hadmissible 0)

theorem signedCancellation_globalSchedule_hasMissedCancellation :
    dagScheduleHasMissedCancellationAtSomeNode signedCancellationGraph
      signedCancellationParentError signedCancellationArrival
      signedCancellationNodeTime := by
  exact ⟨0, signedCancellation_inadmissible_but_exact_negative_example.2.2⟩

/-- Global negative fixture: numerical exactness at every node can coexist
with edge-counting inadmissibility, and the classification identifies the
responsible cancellation node. -/
theorem signedCancellation_global_exact_but_inadmissible_classified :
    dagScheduleExactAtEveryNode signedCancellationGraph
        signedCancellationParentError signedCancellationArrival
        signedCancellationNodeTime ∧
      ¬ dagScheduleAdmissibleAtEveryNode signedCancellationGraph
        signedCancellationArrival signedCancellationNodeTime ∧
      dagScheduleHasMissedCancellationAtSomeNode signedCancellationGraph
        signedCancellationParentError signedCancellationArrival
        signedCancellationNodeTime :=
  ⟨signedCancellation_globalSchedule_exact,
    signedCancellation_globalSchedule_not_admissible,
    signedCancellation_globalSchedule_hasMissedCancellation⟩

/-- If the `-1` edge arrives but the `1` edge does not, the omitted sum is
nonzero and the schedule is correctly detected as inexact. -/
def signedNoncancellingArrival : Fin 3 → ℕ :=
  fun e => if e.val = 1 then 1 else 0

theorem signedNoncancelling_schedule_failure_positive_example :
    dagMissedParentAggregate signedCancellationGraph signedCancellationParentError
        signedNoncancellingArrival 0 0 = 1 ∧
      dagScheduledParentAggregate signedCancellationGraph
          signedCancellationParentError signedNoncancellingArrival 0 0 = 1 ∧
      dagFullParentAggregate signedCancellationGraph
          signedCancellationParentError 0 = 2 ∧
      dagScheduledParentAggregate signedCancellationGraph
          signedCancellationParentError signedNoncancellingArrival 0 0 ≠
        dagFullParentAggregate signedCancellationGraph
          signedCancellationParentError 0 := by
  norm_num [dagMissedParentAggregate, dagScheduledParentAggregate,
    dagFullParentAggregate, dagParentContribution, signedCancellationGraph,
    signedCancellationParentError, signedNoncancellingArrival,
    Fin.sum_univ_succ]

/-- Missing only the `+1` edge leaves a nonzero target-group gain, so this
schedule is not structurally exact. -/
theorem signedNoncancelling_schedule_not_universallyExact :
    ¬ dagScheduleUniversallyExactAtNode signedCancellationGraph
      signedNoncancellingArrival 0 0 := by
  rw [dagScheduleUniversallyExactAtNode_iff_targetGain_zero]
  push Not
  refine ⟨1, ?_⟩
  norm_num [dagMissedTargetGain, signedCancellationGraph,
    signedNoncancellingArrival, Fin.sum_univ_succ]

/-- A zero-gain omitted edge is another exact-but-inadmissible boundary. -/
noncomputable def zeroContributionGraph : SharedLatentDAG (Fin 2) (Fin 2) where
  source := fun _ => 0
  target := fun _ => 1
  rank := fun n => n.val
  forward := by
    intro e
    fin_cases e <;> norm_num
  gain := fun e => if e.val = 0 then 2 else 0
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {1}

def zeroContributionArrival : Fin 2 → ℕ :=
  fun e => if e.val = 0 then 0 else 1

theorem zeroContribution_inadmissible_but_exact_negative_example :
    ¬ dagScheduleAdmissible zeroContributionGraph zeroContributionArrival 0 0 ∧
      dagScheduledParentAggregate zeroContributionGraph
          signedCancellationParentError zeroContributionArrival 0 0 =
        dagFullParentAggregate zeroContributionGraph
          signedCancellationParentError 0 := by
  constructor
  · intro hadmissible
    have hedge := hadmissible 1 (by norm_num [zeroContributionGraph])
    norm_num [zeroContributionArrival] at hedge
  · norm_num [dagScheduledParentAggregate, dagFullParentAggregate,
      dagParentContribution, zeroContributionGraph, zeroContributionArrival,
      signedCancellationParentError, Fin.sum_univ_succ]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
