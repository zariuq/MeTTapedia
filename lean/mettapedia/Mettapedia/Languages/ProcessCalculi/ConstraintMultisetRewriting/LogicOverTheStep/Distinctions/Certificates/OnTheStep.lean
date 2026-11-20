import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Dual
import Mettapedia.GSLT.Distinction.Probabilistic.Completion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionProbability

/-!
# Certificates about a region of the transform step

The transform step under a stochastic policy is a probabilistic system on its states
(`DistinctionProbability.system`): the policy `law` gives each label and state a sub-distribution of
successors (the missing mass is refusal), and a state observes its reading. On a finite region of
states closed under the policy, that system is a finite chain, and the certificates of this folder
are checked on it by the same functions.

* **A closed region** (`ClosedRegion`) lists finitely many states without repetition, so that every
  successor of positive probability of a listed state is listed. Its steps carry the whole mass of
  the policy's steps (`ClosedRegion.mass_eq`), and the policy restricted to it is a finite
  probabilistic system (`regionSystem`): the region's states, the restricted policy, and for every
  listed state `r'` the observation "reads as `r'`".
* **It is the step's system on the region.** Masses of every event on states are the region's masses
  of the listed states in it (`regionSystem_prob`), observations are the step's (`regionSystem_observes`),
  and two listed states are Larsen–Skou bisimilar in the region exactly when they are in the step's
  system (`lsBisimilar_region_iff`). So the behavioural metric of the region (the tree's
  `behaviouralMetric`, the Kantorovich fixed point of the stopped completion) vanishes exactly on
  the step's Larsen–Skou bisimilarity (`behaviouralMetric_region_eq_zero_iff`).
* **Rational data** (`RegionData`) give masses between listed states and which listed states read
  alike; they describe the region when they agree with the policy and the readings
  (`RegionData.Describes`). Their chain (`RegionData.chain`, the listed states and a stop state taking
  the missing mass) read in the reals is the tree's completion of the region
  (`completion_eq_realChain`).
* **So a certificate about the region is checked by the same function**: an accepted prefixpoint
  bounds the region's behavioural metric (`check_sound_region`), a test gap bounds it from below
  (`testGap_le_region`), an accepted dual post-fixpoint bounds it from below at `c < 1`
  (`dualCheck_sound_region`), and when they meet it is exact (`behaviouralMetric_eq_of_meet_region`).
* With a policy whose positive mass lies on actual firings (`DistinctionProbability.SoundSupport`),
  every step of positive mass of the region's chain is a firing of the step (`chain_step_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Interface
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.Cybernetics.ApproximateAdequacy

universe uOb uT uH uO uS uF uL uV uR

variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL} {V : Type uV}

/-! ## Closed regions -/

/-- **A finite region of states closed under a policy**: a listing `point` of states without
repetition such that every successor of positive probability of a listed state, under every label,
is listed. -/
structure ClosedRegion (law : L → State → SubDistribution State) (R : Type uR) where
  point : R → State
  injective : Function.Injective point
  closed : ∀ a r u, 0 < (law a (point r)).weight u → ∃ r', point r' = u

section Region

variable {law : L → State → SubDistribution State} {R : Type uR} [Fintype R]
  (region : ClosedRegion law R)

open Classical in
/-- **The listed states carry the whole mass** of a step from a listed state. -/
theorem ClosedRegion.mass_eq (a : L) (r : R) (C : State → Prop) :
    (law a (region.point r)).mass C =
      ∑ r', if C (region.point r') then (law a (region.point r)).weight (region.point r') else 0 := by
  unfold SubDistribution.mass
  have image : ∑ u ∈ Finset.univ.image region.point,
      (if C u then (law a (region.point r)).weight u else 0) =
      ∑ r', if C (region.point r') then (law a (region.point r)).weight (region.point r') else 0 :=
    Finset.sum_image fun x _ y _ same => region.injective same
  rw [← image]
  apply Finset.sum_subset
  · intro u member
    obtain ⟨r', rfl⟩ := region.closed a r u ((law a (region.point r)).weight_pos member)
    exact Finset.mem_image_of_mem _ (Finset.mem_univ r')
  · intro u _ outside
    rw [Finsupp.notMem_support_iff.mp outside]
    simp

theorem ClosedRegion.total_eq (a : L) (r : R) :
    (law a (region.point r)).total = ∑ r', (law a (region.point r)).weight (region.point r') := by
  rw [← (law a (region.point r)).mass_true, region.mass_eq a r]
  simp

/-- **The policy restricted to the region.** -/
noncomputable def ClosedRegion.kernel (a : L) (r : R) : SubDistribution R :=
  SubDistribution.ofFunction (fun r' => (law a (region.point r)).weight (region.point r'))
    (fun _ => (law a (region.point r)).nonneg _)
    (by rw [← region.total_eq]; exact (law a (region.point r)).total_le_one')

@[simp] theorem ClosedRegion.kernel_weight (a : L) (r r' : R) :
    (region.kernel a r).weight r' = (law a (region.point r)).weight (region.point r') := by
  simp [ClosedRegion.kernel]

variable (read : State → V)

/-- **The step's system on a closed region**: the listed states, the restricted policy, and for every
listed state `r'` the observation "reads as `r'`". -/
noncomputable abbrev regionSystem : ProbabilisticSystem (stateGSLT R) where
  Atom := R
  observes r' r := read (region.point r) = read (region.point r')
  observes_resp _ left right equivalent := by
    have same : left = right := equivalent
    rw [same]
  Label := L
  kernel a r := region.kernel a r
  kernel_resp _ left right equivalent _ _ := by
    have same : left = right := equivalent
    rw [same]

variable (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)

/-- **The region's masses are the step's masses**: the mass of a step from a listed state on an
event of states is the region's mass of the listed states in the event. -/
theorem regionSystem_prob (a : L) (r : R) (C : State → Prop) :
    (DistinctionProbability.system P offers read law).prob a (region.point r) C =
      (regionSystem region read).prob a r (fun r' => C (region.point r')) := by
  classical
  change (law a (region.point r)).mass C = (region.kernel a r).mass (fun r' => C (region.point r'))
  rw [region.mass_eq, SubDistribution.mass_eq_sum]
  simp

/-- **The region's observations are the step's.** -/
theorem regionSystem_observes (r' r : R) :
    (regionSystem region read).observes r' r ↔
      (DistinctionProbability.system P offers read law).observes (read (region.point r'))
        (region.point r) :=
  Iff.rfl

/-- **Bisimilar in the region exactly when bisimilar in the step's system.** -/
theorem lsBisimilar_region_iff {r r' : R} :
    (regionSystem region read).LSBisimilar r r' ↔
      (DistinctionProbability.system P offers read law).LSBisimilar (region.point r)
        (region.point r') := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    let lifted : State → State → Prop := fun u v =>
      u = v ∨ ∃ x y, region.point x = u ∧ region.point y = v ∧ relation x y
    have equivalence : Equivalence lifted := by
      refine ⟨fun u => Or.inl rfl, fun {u v} uv => ?_, fun {u v w} uv vw => ?_⟩
      · rcases uv with same | ⟨x, y, hx, hy, rel⟩
        · exact Or.inl same.symm
        · exact Or.inr ⟨y, x, hy, hx, bisimulation.equivalence.symm rel⟩
      · rcases uv with same | ⟨x, y, hx, hy, rel⟩
        · subst same
          exact vw
        · rcases vw with same' | ⟨y', z, hy', hz, rel'⟩
          · subst same'
            exact Or.inr ⟨x, y, hx, hy, rel⟩
          · have middle : y = y' := region.injective (hy.trans hy'.symm)
            subst middle
            exact Or.inr ⟨x, z, hx, hz, bisimulation.equivalence.trans rel rel'⟩
    refine ⟨lifted, ⟨equivalence, fun {u v} same => Or.inl same, fun {u v} uv value => ?_,
      fun {u v} uv a C closed => ?_⟩, Or.inr ⟨r, r', rfl, rfl, related⟩⟩
    · rcases uv with same | ⟨x, y, rfl, rfl, rel⟩
      · subst same
        exact Iff.rfl
      · have reads : read (region.point y) = read (region.point x) :=
          (bisimulation.observes rel x).mp rfl
        change read (region.point x) = value ↔ read (region.point y) = value
        rw [reads]
    · rcases uv with same | ⟨x, y, rfl, rfl, rel⟩
      · subst same
        rfl
      · have closed' : ProbabilisticSystem.ClosedUnder (S := stateGSLT R) relation
            (fun r'' => C (region.point r'')) :=
          fun x' y' rel' => closed _ _ (Or.inr ⟨x', y', rfl, rfl, rel'⟩)
        exact (regionSystem_prob region read P offers a x C).trans
          ((bisimulation.masses rel a _ closed').trans
            (regionSystem_prob region read P offers a y C).symm)
  · rintro ⟨relation, bisimulation, related⟩
    let restricted : R → R → Prop := fun x y => relation (region.point x) (region.point y)
    refine ⟨restricted, ⟨⟨fun x => bisimulation.equivalence.refl _,
      fun rel => bisimulation.equivalence.symm rel, fun first second =>
        bisimulation.equivalence.trans first second⟩,
      fun {x y} same => ?_, fun {x y} rel z => ?_, fun {x y} rel a C closed => ?_⟩, related⟩
    · have equal : x = y := same
      subst equal
      exact bisimulation.equivalence.refl _
    · exact bisimulation.observes rel (read (region.point z))
    · let widened : State → Prop := fun u => ∃ z, C z ∧ relation (region.point z) u
      have pullback : (fun w => widened (region.point w)) = C := by
        funext w
        apply propext
        constructor
        · rintro ⟨z, holds, rel'⟩
          exact (closed z w rel').mp holds
        · intro holds
          exact ⟨w, holds, bisimulation.equivalence.refl _⟩
      have widened_closed : ProbabilisticSystem.ClosedUnder relation widened := by
        intro u v uv
        constructor
        · rintro ⟨z, holds, rel'⟩
          exact ⟨z, holds, bisimulation.equivalence.trans rel' uv⟩
        · rintro ⟨z, holds, rel'⟩
          exact ⟨z, holds, bisimulation.equivalence.trans rel' (bisimulation.equivalence.symm uv)⟩
      have masses := bisimulation.masses rel a widened widened_closed
      rw [regionSystem_prob region read P offers, regionSystem_prob region read P offers,
        pullback] at masses
      exact masses

/-- **The region's behavioural metric vanishes exactly on the step's Larsen–Skou bisimilarity**, at
every discount `0 < c ≤ 1`. -/
theorem behaviouralMetric_region_eq_zero_iff [Fintype L] [DecidableEq R] {c : ℝ} (c_pos : 0 < c)
    (c_le : c ≤ 1) {r r' : R} :
    behaviouralMetric (M := regionSystem region read) c r r' = 0 ↔
      (DistinctionProbability.system P offers read law).LSBisimilar (region.point r)
        (region.point r') :=
  (behaviouralMetric_eq_zero_iff c_pos c_le).trans (lsBisimilar_region_iff region read P offers)

end Region

/-! ## Rational data for a region and its chain -/

/-- **Rational data for a region**: masses between listed states, and which listed states read
alike. -/
structure RegionData (L : Type uL) (R : Type uR) [Fintype R] where
  mass : L → R → R → ℚ
  nonneg : ∀ a r r', 0 ≤ mass a r r'
  total_le : ∀ a r, ∑ r', mass a r r' ≤ 1
  readsAlike : R → R → Bool

section Data

variable {R : Type uR} [Fintype R] [DecidableEq R]

/-- The steps of the chain of region data: the stop state stays, and a listed state sends its
missing mass to the stop state. -/
def RegionData.trans (data : RegionData L R) (a : L) : Option R → Option R → ℚ
  | none => fun x => if x = none then 1 else 0
  | some r => fun
      | none => 1 - ∑ r', data.mass a r r'
      | some r' => data.mass a r r'

/-- The observations of the chain of region data: "stopped", and "reads as `r'`". -/
def RegionData.observe (data : RegionData L R) : Option R → Option R → ℚ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some r', some r => if data.readsAlike r' r then 1 else 0

theorem RegionData.isDistribution_trans (data : RegionData L R) (a : L) (s : Option R) :
    IsDistribution (data.trans a s) := by
  rcases s with _ | r
  · refine ⟨fun x => ?_, ?_⟩
    · simp only [RegionData.trans]
      split_ifs <;> norm_num
    · simp [RegionData.trans]
  · refine ⟨fun x => ?_, ?_⟩
    · rcases x with _ | r'
      · have total := data.total_le a r
        simp only [RegionData.trans]
        linarith
      · exact data.nonneg a r r'
    · simp only [RegionData.trans, Fintype.sum_option]
      ring

/-- **The chain of region data**: the listed states and a stop state. -/
def RegionData.chain (data : RegionData L R) : LabelledMarkovChain ℚ L (Option R) (Option R) where
  trans := data.trans
  isDistribution := data.isDistribution_trans
  observe := data.observe

variable {law : L → State → SubDistribution State} (region : ClosedRegion law R) (read : State → V)

/-- **The data describe the region**: the masses are the policy's and the readings are the step's. -/
def RegionData.Describes (data : RegionData L R) : Prop :=
  (∀ a r r', (law a (region.point r)).weight (region.point r') = (data.mass a r r' : ℝ)) ∧
    ∀ r' r, data.readsAlike r' r = true ↔ read (region.point r) = read (region.point r')

/-- **The region's completion is the real chain of the data.** -/
theorem completion_eq_realChain {data : RegionData L R} (describes : data.Describes region read) :
    completion (regionSystem region read) = realChain data.chain := by
  classical
  apply eq_realChain
  · intro a s x
    rcases s with _ | r
    · rcases x with _ | x <;> simp [completion, completionTrans, RegionData.chain, RegionData.trans,
        dirac]
    · rcases x with _ | x
      · change 1 - (region.kernel a r).total = ((1 - ∑ r', data.mass a r r' : ℚ) : ℝ)
        rw [SubDistribution.total_eq_sum]
        simp [describes.1]
      · change (region.kernel a r).weight x = (data.mass a r x : ℝ)
        rw [ClosedRegion.kernel_weight, describes.1]
  · intro i s
    rcases i with _ | r' <;> rcases s with _ | r
    · simp [completion, completionObserve, RegionData.chain, RegionData.observe]
    · simp [completion, completionObserve, RegionData.chain, RegionData.observe]
    · simp [completion, completionObserve, RegionData.chain, RegionData.observe]
    · change (if read (region.point r) = read (region.point r') then (1 : ℝ) else 0) =
        ((if data.readsAlike r' r then 1 else 0 : ℚ) : ℝ)
      by_cases alike : data.readsAlike r' r = true
      · rw [if_pos ((describes.2 r' r).mp alike), if_pos alike]
        norm_num
      · rw [if_neg (fun same => alike ((describes.2 r' r).mpr same)), if_neg alike]
        norm_num

variable [Fintype L] {data : RegionData L R}

/-- **An accepted prefixpoint of the region's chain bounds the region's behavioural metric**, at every
discount `0 ≤ c`. -/
theorem check_sound_region (describes : data.Describes region read) {c : ℚ}
    {cert : Prefixpoint L (Option R)} (accepted : check data.chain c cert = true) (c_nonneg : 0 ≤ c)
    (r r' : R) :
    behaviouralMetric (M := regionSystem region read) (c : ℝ) r r' ≤
      (cert.kernel (some r) (some r') : ℝ) := by
  unfold behaviouralMetric
  rw [completion_eq_realChain region read describes]
  exact check_sound accepted c_nonneg (some r) (some r')

/-- **A test's gap on the region's chain bounds the region's behavioural metric from below**, at every
discount `0 ≤ c ≤ 1`. -/
theorem testGap_le_region (describes : data.Describes region read) {c : ℚ}
    {nodes : List (TestNode L (Option R))} {r r' : R} {g : ℚ} {d : ℕ}
    (gap : testGap data.chain c nodes (some r) (some r') = some (g, d)) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) :
    (g : ℝ) ≤ behaviouralMetric (M := regionSystem region read) (c : ℝ) r r' := by
  unfold behaviouralMetric
  rw [completion_eq_realChain region read describes]
  exact testGap_le_bisimulationMetric gap c_nonneg c_le

/-- **An accepted dual post-fixpoint of the region's chain bounds the region's behavioural metric
from below**, at every discount `0 ≤ c < 1`. -/
theorem dualCheck_sound_region (describes : data.Describes region read) {c : ℚ}
    {dual : DualPostfixpoint L (Option R)} (accepted : dualCheck data.chain c dual = true)
    (c_nonneg : 0 ≤ c) (c_lt : c < 1) (r r' : R) :
    (dual.kernel (some r) (some r') : ℝ) ≤ behaviouralMetric (M := regionSystem region read) (c : ℝ) r r' := by
  unfold behaviouralMetric
  rw [completion_eq_realChain region read describes]
  exact dualCheck_sound accepted c_nonneg c_lt (some r) (some r')

/-- **Exact when a test meets the prefixpoint**, at every discount `0 ≤ c ≤ 1`. -/
theorem behaviouralMetric_eq_of_meet_region (describes : data.Describes region read) {c : ℚ}
    {cert : Prefixpoint L (Option R)} (accepted : check data.chain c cert = true)
    {nodes : List (TestNode L (Option R))} {r r' : R} {g : ℚ} {d : ℕ}
    (gap : testGap data.chain c nodes (some r) (some r') = some (g, d))
    (meet : g = cert.kernel (some r) (some r')) (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    behaviouralMetric (M := regionSystem region read) (c : ℝ) r r' = (g : ℝ) := by
  unfold behaviouralMetric
  rw [completion_eq_realChain region read describes]
  exact bisimulationMetric_eq_of_meet accepted gap meet c_nonneg c_le

omit [Fintype L] in
/-- **Under a policy over actual firings, every step of positive mass of the region's chain between
listed states is a firing of the step.** -/
theorem chain_step_fires (P : Interface.Step X O State Fir)
    (offers : L → (s : State) → Fir s → Prop)
    (sound : DistinctionProbability.SoundSupport P offers law)
    (describes : data.Describes region read) {a : L} {r r' : R}
    (positive : 0 < data.chain.trans a (some r) (some r')) :
    Race.Generic.Moves P offers (region.point r) a (region.point r') := by
  apply sound a (region.point r) (region.point r')
  rw [describes.1]
  exact_mod_cast positive

end Data

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
