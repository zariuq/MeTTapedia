import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsRounds
import Mettapedia.Algebra.ResourceValuations

/-!
# Peak occupancy in the prefix-maximum monoid, and round boundaries

## The prefix-maximum monoid

An occupancy **profile** (`Peak`) is a net change of the number of present occurrences and the peak
above the start, with `0 ≤ peak` and `net ≤ peak`. Profiles compose in run order by
`(n, p) · (n', p') = (n + n', max p (n + p'))`: the second's peak is raised by the first's net
change. This is a monoid, and it is not commutative.

A firing's profile (`stepOf`) is its net change, what it makes minus what it takes, with the peak at
the larger end. The profile of a run (`profile`) is the product of its firings' profiles. It is
exact for executable runs:

* the run ends at the start plus its net change (`card_follow`);
* every configuration the run passes lies at most its peak above the start (`prefix_card_le`);
* some configuration attains the peak (`peak_attained`).

For balanced phases the product is the sequential peak of `Algebra.ResourceValuations`
(`balanced_mul`).

## Peak is not a property of the trace

A consumer of the one present occurrence and a producer of a new one form a round. Consumer first,
the occupancy goes 1 → 0 → 1 and peaks at 1; producer first, it goes 1 → 2 → 1 and peaks at 2
(`PeakControls.peak_one_then_two`). The two orders are one contextual trace.

## Round boundaries

A run recorded with its **round boundaries** (`RoundRun`) is a list of rounds, each a round where
the earlier ones left the configuration. Observed at the boundaries, each round contributes only
its net change (`roundStep`), and the **boundary profile** (`boundaryProfile`)

* does not depend on the order within any round (`boundaryProfile_forall₂_perm`): it is a property
  of the round decomposition;
* has the same net change as every linearization and a peak below it
  (`boundaryProfile_le_profile`);
* bounds the sequential peak of each round by the sum of its members' positive changes
  (`profile_peak_le_positive`): round peaks add as a bound.

In the control the boundary profile peaks at 0 above the start in both orders of the round, while
the sequential peaks are 0 and 1 (`PeakControls.boundary_profile_order_free`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-! ## The prefix-maximum monoid -/

/-- **An occupancy profile**: the net change of the number of present occurrences, and the peak
above the start. -/
@[ext] structure Peak where
  net : ℤ
  peak : ℤ
  nonneg : 0 ≤ peak
  net_le : net ≤ peak

namespace Peak

instance : One Peak := ⟨⟨0, 0, le_refl _, le_refl _⟩⟩

/-- Run one profile after another: the second's peak is raised by the first's net change. -/
instance : Mul Peak := ⟨fun x y => ⟨x.net + y.net, max x.peak (x.net + y.peak),
  le_max_of_le_left x.nonneg, le_max_of_le_right (by linarith [y.net_le])⟩⟩

@[simp] theorem one_net : (1 : Peak).net = 0 := rfl
@[simp] theorem one_peak : (1 : Peak).peak = 0 := rfl
@[simp] theorem mul_net (x y : Peak) : (x * y).net = x.net + y.net := rfl
@[simp] theorem mul_peak (x y : Peak) : (x * y).peak = max x.peak (x.net + y.peak) := rfl

instance : Monoid Peak where
  mul_assoc x y z := by
    ext
    · simp [add_assoc]
    · simp only [mul_peak, mul_net]
      rw [max_assoc, add_assoc, max_add_add_left]
  one_mul x := by
    ext
    · simp
    · simp [max_eq_right x.nonneg]
  mul_one x := by
    ext
    · simp
    · simp [max_eq_left x.net_le]

/-- **The prefix-maximum monoid is not commutative.** -/
theorem not_comm : ∃ x y : Peak, x * y ≠ y * x := by
  refine ⟨⟨-1, 0, le_refl _, by decide⟩, ⟨1, 1, by decide, le_refl _⟩, fun same => ?_⟩
  have := congrArg Peak.peak same
  simp at this

/-- A peak is monotone in both factors with the net change of the first fixed. -/
theorem mul_peak_le {x x' y y' : Peak} (net : x.net = x'.net) (first : x.peak ≤ x'.peak)
    (second : y.peak ≤ y'.peak) : (x * y).peak ≤ (x' * y').peak := by
  simp only [mul_peak]
  rw [net]
  exact max_le_max first (by linarith)

/-- A balanced phase: it frees what it allocates, and peaks at `p`. -/
def balanced (p : ℕ) : Peak := ⟨0, p, Nat.cast_nonneg p, Nat.cast_nonneg p⟩

/-- **Balanced phases compose by the sequential peak of `ResourceValuations`.** -/
theorem balanced_mul (p q : ℕ) :
    balanced p * balanced q = balanced (Mettapedia.Algebra.peakSequential p q) := by
  ext
  · simp [balanced]
  · simp [balanced, Mettapedia.Algebra.peakSequential]

end Peak

/-! ## The profile of a run -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- The net change of occupancy of a firing: what it makes minus what it takes. -/
def netOf (f : Firing T S O) : ℤ := f.selection.made.length - f.selection.taken.length

/-- The profile of one firing. -/
def stepOf (f : Firing T S O) : Peak :=
  ⟨netOf f, max 0 (netOf f), le_max_left _ _, le_max_right _ _⟩

/-- **The profile of a run**: the product of its firings' profiles, in run order. -/
def profile (w : List (Firing T S O)) : Peak := (w.map stepOf).prod

@[simp] theorem profile_nil : profile ([] : List (Firing T S O)) = 1 := rfl

@[simp] theorem profile_cons (f : Firing T S O) (w : List (Firing T S O)) :
    profile (f :: w) = stepOf f * profile w := by
  simp [profile]

theorem profile_append (u v : List (Firing T S O)) : profile (u ++ v) = profile u * profile v := by
  simp [profile, List.prod_append]

theorem profile_net (w : List (Firing T S O)) : (profile w).net = (w.map netOf).sum := by
  induction w with
  | nil => rfl
  | cons f w ih => simp [ih, stepOf]

section Occupancy

variable [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)

/-- **A firing changes the number of present occurrences by its net change.** -/
theorem card_result {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C) :
    ((f.result label C).present.card : ℤ) = C.present.card + netOf f := by
  have enabled := valid.firing.occurrences
  have takenCard : f.selection.taken.toFinset.card = f.selection.taken.length :=
    List.toFinset_card_of_nodup valid.firing.take_distinct
  have madeCard : f.selection.made.toFinset.card = f.selection.made.length :=
    List.toFinset_card_of_nodup valid.firing.output_distinct
  have subset : f.selection.taken.toFinset ⊆ C.present := enabled.taken_subset
  have apart : Disjoint (C.present \ f.selection.taken.toFinset) f.selection.made.toFinset :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset enabled.fresh.symm
  have count : (f.result label C).present.card =
      (C.present.card - f.selection.taken.length) + f.selection.made.length := by
    change ((C.present \ f.selection.taken.toFinset) ∪ f.selection.made.toFinset).card = _
    rw [Finset.card_union_of_disjoint apart, Finset.card_sdiff_of_subset subset, takenCard, madeCard]
  have le : f.selection.taken.length ≤ C.present.card := takenCard ▸ Finset.card_le_card subset
  rw [count]
  unfold netOf
  omega

/-- **A run ends at the start plus its net change.** -/
theorem card_follow : ∀ (C : Configuration T O) (w : List (Firing T S O)),
    Executable A label C w →
      ((follow label C w).present.card : ℤ) = C.present.card + (profile w).net
  | C, [], _ => by simp [follow]
  | C, f :: rest, ⟨valid, later⟩ => by
      change ((follow label (f.result label C) rest).present.card : ℤ) = _
      rw [card_follow _ rest later, card_result A label valid, profile_cons, Peak.mul_net]
      simp only [stepOf]
      ring

/-- **No configuration of a run lies more than its peak above the start.** -/
theorem prefix_card_le : ∀ (C : Configuration T O) (u v : List (Firing T S O)),
    Executable A label C (u ++ v) →
      ((follow label C u).present.card : ℤ) ≤ C.present.card + (profile (u ++ v)).peak
  | C, [], v, _ => by
      simp only [follow, List.nil_append]
      linarith [(profile v).nonneg]
  | C, f :: u, v, ⟨valid, later⟩ => by
      have ih := prefix_card_le (f.result label C) u v later
      rw [card_result A label valid] at ih
      change ((follow label (f.result label C) u).present.card : ℤ) ≤
        C.present.card + (profile (f :: (u ++ v))).peak
      rw [profile_cons, Peak.mul_peak]
      have := le_max_right (stepOf f).peak ((stepOf f).net + (profile (u ++ v)).peak)
      simp only [stepOf] at this ⊢
      linarith

/-- **Some configuration of a run attains its peak.** -/
theorem peak_attained : ∀ (C : Configuration T O) (w : List (Firing T S O)),
    Executable A label C w →
      ∃ u v, w = u ++ v ∧ ((follow label C u).present.card : ℤ) = C.present.card + (profile w).peak
  | C, [], _ => ⟨[], [], rfl, by simp [follow]⟩
  | C, f :: rest, ⟨valid, later⟩ => by
      obtain ⟨u, v, rfl, attained⟩ := peak_attained (f.result label C) rest later
      rw [card_result A label valid] at attained
      have shape : (profile (f :: (u ++ v))).peak =
          max (max 0 (netOf f)) (netOf f + (profile (u ++ v)).peak) := by
        rw [profile_cons, Peak.mul_peak]
        rfl
      rcases le_total (max 0 (netOf f)) (netOf f + (profile (u ++ v)).peak) with high | low
      · refine ⟨f :: u, v, rfl, ?_⟩
        change ((follow label (f.result label C) u).present.card : ℤ) = _
        rw [attained, shape, max_eq_right high]
        ring
      · rcases le_total 0 (netOf f) with positive | negative
        · refine ⟨[f], u ++ v, rfl, ?_⟩
          change ((f.result label C).present.card : ℤ) = _
          rw [card_result A label valid, shape, max_eq_left low, max_eq_right positive]
        · refine ⟨[], f :: (u ++ v), rfl, ?_⟩
          change (C.present.card : ℤ) = _
          rw [shape, max_eq_left low, max_eq_left negative]
          ring

end Occupancy

/-! ## Round boundaries -/

/-- **The profile of a round observed at its boundaries**: only its net change. -/
def roundStep (round : List (Firing T S O)) : Peak :=
  ⟨(round.map netOf).sum, max 0 (round.map netOf).sum, le_max_left _ _, le_max_right _ _⟩

/-- **The boundary profile** of a run recorded with its round boundaries. -/
def boundaryProfile (rounds : List (List (Firing T S O))) : Peak := (rounds.map roundStep).prod

theorem roundStep_perm {round round' : List (Firing T S O)} (perm : round.Perm round') :
    roundStep round = roundStep round' := by
  have same : (round.map netOf).sum = (round'.map netOf).sum := (perm.map netOf).sum_eq
  ext
  · exact same
  · simp only [roundStep, same]

/-- **The boundary profile does not depend on the order within any round.** -/
theorem boundaryProfile_forall₂_perm {rounds rounds' : List (List (Firing T S O))}
    (perms : List.Forall₂ List.Perm rounds rounds') :
    boundaryProfile rounds = boundaryProfile rounds' := by
  induction perms with
  | nil => rfl
  | cons perm _ ih =>
      simp only [boundaryProfile, List.map_cons, List.prod_cons] at ih ⊢
      rw [roundStep_perm perm, ih]

theorem roundStep_le_profile (round : List (Firing T S O)) :
    (roundStep round).net = (profile round).net ∧ (roundStep round).peak ≤ (profile round).peak := by
  have net := (profile_net round).symm
  refine ⟨net, ?_⟩
  change max 0 (round.map netOf).sum ≤ (profile round).peak
  rw [← profile_net]
  exact max_le (profile round).nonneg (profile round).net_le

/-- **The boundary profile has the net change of the run and a peak below it.** -/
theorem boundaryProfile_le_profile (rounds : List (List (Firing T S O))) :
    (boundaryProfile rounds).net = (profile rounds.flatten).net ∧
      (boundaryProfile rounds).peak ≤ (profile rounds.flatten).peak := by
  induction rounds with
  | nil => exact ⟨rfl, le_refl _⟩
  | cons round rest ih =>
      have step := roundStep_le_profile round
      have splitProfile : profile (round :: rest).flatten = profile round * profile rest.flatten := by
        rw [List.flatten_cons, profile_append]
      have splitBoundary : boundaryProfile (round :: rest) = roundStep round * boundaryProfile rest := by
        simp [boundaryProfile]
      rw [splitProfile, splitBoundary]
      refine ⟨?_, Peak.mul_peak_le step.1 step.2 ih.2⟩
      simp only [Peak.mul_net]
      rw [step.1, ih.1]

/-- **Round peaks add as a bound**: in any order, a run peaks at most the sum of its firings'
positive changes. -/
theorem profile_peak_le_positive (w : List (Firing T S O)) :
    (profile w).peak ≤ (w.map fun f => max 0 (netOf f)).sum := by
  induction w with
  | nil => exact le_refl _
  | cons f w ih =>
      rw [profile_cons, Peak.mul_peak, List.map_cons, List.sum_cons]
      have nonneg : 0 ≤ (w.map fun f => max 0 (netOf f)).sum :=
        List.sum_nonneg fun x member => by
          obtain ⟨g, _, rfl⟩ := List.mem_map.mp member
          exact le_max_left _ _
      have stepPeak : (stepOf f).peak = max 0 (netOf f) := rfl
      have stepNet : (stepOf f).net = netOf f := rfl
      rw [stepPeak, stepNet]
      refine max_le (by linarith) ?_
      linarith [le_max_right 0 (netOf f)]

section Boundaries

variable [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)

/-- **A run recorded with its round boundaries**: each block is a round where the earlier blocks
left the configuration. -/
def RoundRun : Configuration T O → List (List (Firing T S O)) → Prop
  | C, [] => A.Consistent C.equations
  | C, round :: rest => Round A label C round ∧ RoundRun (follow label C round) rest

theorem follow_append' : ∀ (C : Configuration T O) (u v : List (Firing T S O)),
    follow label C (u ++ v) = follow label (follow label C u) v
  | _, [], _ => rfl
  | C, f :: u, v => follow_append' (f.result label C) u v

theorem executable_append' : ∀ (C : Configuration T O) (u v : List (Firing T S O)),
    Executable A label C u → Executable A label (follow label C u) v →
      Executable A label C (u ++ v)
  | _, [], _, _, later => later
  | C, f :: u, v, ⟨valid, rest⟩, later => ⟨valid, executable_append' (f.result label C) u v rest later⟩

/-- **A run recorded with round boundaries is a run**: its linearization is executable. -/
theorem RoundRun.executable : ∀ {C : Configuration T O} {rounds : List (List (Firing T S O))},
    RoundRun A label C rounds → Executable A label C rounds.flatten
  | _, [], consistent => consistent
  | C, round :: rest, ⟨isRound, later⟩ => by
      rw [List.flatten_cons]
      exact executable_append' A label C round _ (isRound.executable A label)
        (RoundRun.executable later)

end Boundaries

/-! ## Controls -/

namespace PeakControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (Run)

/-- Every occurrence is labelled `0`. -/
def label : Nat → Term signature := fun _ => .const 0

/-- Takes occurrence `0`. -/
def consumer : Run := ⟨⟨[.const 0], [], [], [], []⟩, [], ⟨[0], [], []⟩⟩

/-- Makes occurrence `1`. -/
def producer : Run := ⟨⟨[], [], [], [], [.const 0]⟩, [], ⟨[], [], [1]⟩⟩

/-- One present occurrence. -/
def start : Configuration (Term signature) Nat := ⟨[], {0}⟩

theorem consumer_problem (σ : Subst signature) (D : Configuration (Term signature) Nat)
    (base : A.Models σ D.equations) :
    A.Models σ (consumer.selection.problem label consumer.rule D) := by
  intro equation member
  simp only [Selection.problem, Selection.equations, consumer, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.append_nil, List.mem_append, List.mem_singleton] at member
  rcases member with inBase | rfl
  · exact base equation inBase
  · rfl

theorem consumer_valid : consumer.Valid A label start :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, consumer_problem _ _ (fun _ member => by cases member)⟩,
    by simp [consumer]⟩, by simp [consumer]⟩

theorem producer_valid : producer.Valid A label start :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, start, producer]⟩,
    by simp [producer]⟩, by simp [producer]⟩

/-- The consumer and the producer form a round. -/
theorem consumer_producer_round : Round A label start [consumer, producer] := by
  refine ⟨?_, ⟨Subst.id signature, ?_⟩, List.pairwise_pair.mpr ⟨?_, by simp [consumer],
    by simp [producer], by simp [consumer], by simp [producer]⟩⟩
  · intro f member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact consumer_valid
    · exact producer_valid
  · intro equation member
    simp only [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations,
      start, consumer, producer, List.flatMap_cons, List.flatMap_nil, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.append_nil, List.nil_append, List.mem_singleton] at member
    subst member
    rfl
  · unfold MeTTaCalculus.OccurrenceCommits.Independent MeTTaCalculus.OccurrenceCommits.Clash
      MeTTaCalculus.OccurrenceCommits.Spoils MeTTaCalculus.OccurrenceCommits.WritesInto
    decide

theorem consumer_first_profile : profile [consumer, producer] = ⟨0, 0, le_refl _, le_refl _⟩ := by
  ext <;> simp [profile, stepOf, netOf, consumer, producer]

theorem producer_first_profile : profile [producer, consumer] = ⟨0, 1, by decide, by decide⟩ := by
  ext <;> simp [profile, stepOf, netOf, consumer, producer]

/-- **Negative control: peak is not a property of the trace (1, then 2).** The two orders of the
round of the consumer and the producer are one contextual trace. Consumer first, no
configuration holds more than one occurrence; producer first, a configuration holds two. -/
theorem peak_one_then_two :
    RoundEquiv A label start [consumer, producer] [producer, consumer] ∧
      (∀ u v, [consumer, producer] = u ++ v → (follow label start u).present.card ≤ 1) ∧
      (follow label start [producer]).present.card = 2 := by
  refine ⟨.symm _ _ (consumer_producer_round.orders_equivalent A label (List.Perm.swap _ _ [])),
    fun u v split => ?_, by decide⟩
  have bound := prefix_card_le A label start u v (split ▸ consumer_producer_round.executable A label)
  rw [← split, consumer_first_profile] at bound
  have startCard : start.present.card = 1 := by decide
  rw [startCard] at bound
  have bounded : ((follow label start u).present.card : ℤ) ≤ 1 := by simpa using bound
  exact_mod_cast bounded

/-- **Positive control: round boundaries make the peak order free.** Recorded as one round, the two
orders have the same boundary profile, which peaks at the start, while their sequential profiles
peak at `0` and `1` above it. -/
theorem boundary_profile_order_free :
    RoundRun A label start [[consumer, producer]] ∧ RoundRun A label start [[producer, consumer]] ∧
      boundaryProfile [[consumer, producer]] = boundaryProfile [[producer, consumer]] ∧
      (boundaryProfile [[consumer, producer]]).peak = 0 ∧
      (profile [consumer, producer]).peak = 0 ∧ (profile [producer, consumer]).peak = 1 := by
  have swapped := consumer_producer_round.perm A label (List.Perm.swap producer consumer [])
  refine ⟨⟨consumer_producer_round, ?_⟩, ⟨swapped, ?_⟩,
    boundaryProfile_forall₂_perm (List.Forall₂.cons (List.Perm.swap _ _ []) List.Forall₂.nil),
    by simp [boundaryProfile, roundStep, netOf, consumer, producer],
    by rw [consumer_first_profile], by rw [producer_first_profile]⟩
  · obtain ⟨σ, solved⟩ := (consumer_producer_round.executable A label).2.2
    exact ⟨σ, solved⟩
  · obtain ⟨σ, solved⟩ := (swapped.executable A label).2.2
    exact ⟨σ, solved⟩

end PeakControls

#print axioms Peak.not_comm
#print axioms Peak.mul_peak_le
#print axioms Peak.balanced_mul
#print axioms profile_append
#print axioms profile_net
#print axioms card_result
#print axioms card_follow
#print axioms prefix_card_le
#print axioms peak_attained
#print axioms roundStep_perm
#print axioms boundaryProfile_forall₂_perm
#print axioms boundaryProfile_le_profile
#print axioms profile_peak_le_positive
#print axioms RoundRun.executable
#print axioms PeakControls.peak_one_then_two
#print axioms PeakControls.boundary_profile_order_free

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
