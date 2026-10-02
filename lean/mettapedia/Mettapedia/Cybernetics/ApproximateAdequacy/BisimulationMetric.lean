import Mettapedia.Cybernetics.ApproximateAdequacy.CouplingBound
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# The bisimulation metric of finite labelled Markov chains

The canonical behavioural pseudometric at discount `c`, defined by iterated
Kantorovich liftings (F. van Breugel and J. Worrell; J. Desharnais,
V. Gupta, R. Jagadeesan and P. Panangaden), on finite chains over `ℝ`.

* **The Kantorovich lifting** `kantorovich m μ ν` is the least cost of a
  coupling of `μ` and `ν` for the cost `m`.  On a finite space an optimal
  coupling exists, because the couplings form a compact polytope
  (`exists_optimal_coupling`).
* **The Kantorovich operator** `kantorovichStep` sends `m` to the maximum of
  the observation distance and `c · kantorovich m (τ_a s) (τ_a t)` over the
  actions `a`.  Its iterates from the observation distance increase
  (`approxMetric_mono`), and `bisimulationMetric` is their supremum.

**Theorems.**
* **The metric is the least coupling bound**: it is a coupling bound
  (`couplingBound_bisimulationMetric`) and lies below every coupling bound
  (`bisimulationMetric_le`).  It is a fixed point of the operator
  (`bisimulationMetric_eq_step`) and its least prefixed point
  (`bisimulationMetric_le_of_step_le`); a coupling bound is exactly a
  prefixed point (`couplingBound_iff_step_le`).
* **Soundness of the logical characterisation**: every functional expression
  of depth at most `n` varies by at most the `n`-th iterate
  (`abs_eval_sub_le_approxMetric`), hence by at most the metric
  (`abs_eval_sub_le_bisimulationMetric`).  The converse, that the metric is
  the supremum of these differences, is the theorem of Desharnais, Gupta,
  Jagadeesan and Panangaden; it needs Kantorovich duality and is not proved
  here.
* **Zero distance is probabilistic bisimilarity**, at every discount
  `0 < c ≤ 1` (`bisimulationMetric_eq_zero_iff`).
* **A pseudometric**: zero on the diagonal (`bisimulationMetric_self`),
  symmetric (`bisimulationMetric_comm`), with the triangle inequality
  (`bisimulationMetric_triangle`) from gluing couplings.
* **On deterministic chains at discount `1` it is the Girard–Pappas
  distance** (`bisimulationMetric_ofFunction_le_iff`).

`Classical.choice` enters through `ℝ`, the compactness argument, and Mathlib's
finite-sum lemmas.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset Filter

variable {A Atom S T U : Type*} [Fintype S] [Fintype T] [Fintype U]

/-! ## Reversal and the diagonal, over any field -/

section Generic

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {P : LabelledMarkovChain 𝕜 A Atom S} {Q : LabelledMarkovChain 𝕜 A Atom T} {c : 𝕜}
  {m : S → T → 𝕜}

omit [IsStrictOrderedRing 𝕜] in
/-- **Coupling bounds reverse.** -/
theorem CouplingBound.swap (bound : CouplingBound P Q c m) :
    CouplingBound Q P c fun t s => m s t where
  nonneg t s := bound.nonneg s t
  observe_le i t s := by rw [abs_sub_comm]; exact bound.observe_le i s t
  step_le a t s := by
    obtain ⟨ω, le⟩ := bound.step_le a s t
    exact ⟨ω.swap, by rw [ω.cost_swap]; exact le⟩

/-- The diagonal coupling of a distribution with itself. -/
def Coupling.diagonal [DecidableEq S] {μ : S → 𝕜} (distribution : IsDistribution μ) :
    Coupling μ μ where
  weight x y := if x = y then μ x else 0
  nonneg x y := by split_ifs <;> first | exact distribution.nonneg x | exact le_rfl
  sum_right x := by simp
  sum_left y := by simp

omit [IsStrictOrderedRing 𝕜] in
/-- **Equality is a probabilistic bisimulation of a chain with itself.** -/
theorem isProbabilisticBisimulation_eq [DecidableEq S] :
    IsProbabilisticBisimulation P P Eq := by
  intro s t same
  subst same
  refine ⟨fun _ => rfl, fun a => ⟨Coupling.diagonal (P.isDistribution a s), fun x y positive => ?_⟩⟩
  by_contra different
  exact positive (if_neg different)

end Generic

/-! ## The Kantorovich lifting over `ℝ` -/

section Kantorovich

variable {μ : S → ℝ} {ν : T → ℝ}

/-- **The Kantorovich lifting**: the least cost of a coupling. -/
noncomputable def kantorovich (m : S → T → ℝ) (μ : S → ℝ) (ν : T → ℝ) : ℝ :=
  ⨅ ω : Coupling μ ν, ω.cost m

theorem Coupling.weight_le_one (ω : Coupling μ ν) (distribution : IsDistribution μ) (x : S)
    (y : T) : ω.weight x y ≤ 1 :=
  (ω.weight_le_left x y).trans (distribution.le_one x)

theorem Coupling.neg_sum_abs_le_cost (ω : Coupling μ ν) (distribution : IsDistribution μ)
    (m : S → T → ℝ) : -(∑ x, ∑ y, |m x y|) ≤ ω.cost m := by
  unfold Coupling.cost
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have weight_le := ω.weight_le_one distribution x y
  have product : |ω.weight x y * m x y| ≤ |m x y| := by
    rw [abs_mul, abs_of_nonneg (ω.nonneg x y)]
    exact mul_le_of_le_one_left (abs_nonneg _) weight_le
  linarith [neg_abs_le (ω.weight x y * m x y)]

theorem bddBelow_cost (distribution : IsDistribution μ) (m : S → T → ℝ) :
    BddBelow (Set.range fun ω : Coupling μ ν => ω.cost m) :=
  ⟨-(∑ x, ∑ y, |m x y|), fun _ ⟨ω, same⟩ => same ▸ ω.neg_sum_abs_le_cost distribution m⟩

theorem kantorovich_le (distribution : IsDistribution μ) (m : S → T → ℝ) (ω : Coupling μ ν) :
    kantorovich m μ ν ≤ ω.cost m :=
  ciInf_le (bddBelow_cost distribution m) ω

theorem le_kantorovich (first : IsDistribution μ) (second : IsDistribution ν) {m : S → T → ℝ}
    {b : ℝ} (below : ∀ ω : Coupling μ ν, b ≤ ω.cost m) : b ≤ kantorovich m μ ν :=
  haveI : Nonempty (Coupling μ ν) := ⟨Coupling.independent first second⟩
  le_ciInf below

theorem kantorovich_mono (first : IsDistribution μ) (second : IsDistribution ν)
    {m m' : S → T → ℝ} (le : ∀ x y, m x y ≤ m' x y) : kantorovich m μ ν ≤ kantorovich m' μ ν :=
  le_kantorovich first second fun ω => (kantorovich_le first m ω).trans (ω.cost_mono le)

/-- The lifting moves by at most a uniform perturbation of the cost. -/
theorem kantorovich_le_add (first : IsDistribution μ) (second : IsDistribution ν)
    {m m' : S → T → ℝ} {η : ℝ} (le : ∀ x y, m x y ≤ m' x y + η) :
    kantorovich m μ ν ≤ kantorovich m' μ ν + η := by
  have below : ∀ ω : Coupling μ ν, kantorovich m μ ν - η ≤ ω.cost m' := fun ω => by
    have := (kantorovich_le first m ω).trans (ω.cost_mono le)
    rw [ω.cost_add, ω.cost_const first] at this
    linarith
  linarith [le_kantorovich first second below]

/-- **The lifting bounds the difference of expectations** of functions whose
pointwise differences it lifts: the easy half of Kantorovich duality. -/
theorem abs_expect_sub_le_kantorovich (first : IsDistribution μ) (second : IsDistribution ν)
    {f : S → ℝ} {g : T → ℝ} {m : S → T → ℝ} (bound : ∀ x y, |f x - g y| ≤ m x y) :
    |expect μ f - expect ν g| ≤ kantorovich m μ ν :=
  le_kantorovich first second fun ω => ω.abs_expect_sub_le bound

/-- **Against a point mass the lifting is an expectation.** -/
theorem kantorovich_of_eq_dirac_right [DecidableEq T] (first : IsDistribution μ) {y₀ : T}
    (second : ν = dirac y₀) (m : S → T → ℝ) :
    kantorovich m μ ν = expect μ fun x => m x y₀ := by
  have distribution : IsDistribution ν := second ▸ isDistribution_dirac y₀
  have forced : ∀ ω : Coupling μ ν, ω.cost m = expect μ fun x => m x y₀ := fun ω =>
    ω.cost_of_eq_dirac_right second m
  refine le_antisymm ?_ (le_kantorovich first distribution fun ω => (forced ω).ge)
  rw [← forced (Coupling.independent first distribution)]
  exact kantorovich_le first m _

/-- The couplings of `μ` and `ν`, as a set of joint weightings. -/
def couplingSet (μ : S → ℝ) (ν : T → ℝ) : Set (S → T → ℝ) :=
  {w | (∀ x y, 0 ≤ w x y) ∧ (∀ x, ∑ y, w x y = μ x) ∧ ∀ y, ∑ x, w x y = ν y}

theorem isClosed_couplingSet (μ : S → ℝ) (ν : T → ℝ) : IsClosed (couplingSet μ ν) := by
  have entry : ∀ (x : S) (y : T), Continuous fun w : S → T → ℝ => w x y := fun x y =>
    (continuous_apply y).comp (continuous_apply x)
  have closed : IsClosed ((⋂ x, ⋂ y, {w : S → T → ℝ | 0 ≤ w x y}) ∩
      ((⋂ x, {w : S → T → ℝ | ∑ y, w x y = μ x}) ∩ ⋂ y, {w : S → T → ℝ | ∑ x, w x y = ν y})) :=
    (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (entry x y)).inter
        ((isClosed_iInter fun x => isClosed_eq
            (continuous_finsetSum _ fun y _ => entry x y) continuous_const).inter
          (isClosed_iInter fun y => isClosed_eq
            (continuous_finsetSum _ fun x _ => entry x y) continuous_const))
  convert closed using 1
  ext w
  simp only [couplingSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]

theorem couplingSet_subset_Icc (distribution : IsDistribution μ) :
    couplingSet μ ν ⊆ Set.Icc 0 1 := by
  rintro w ⟨nonneg, rows, _⟩
  refine ⟨fun x y => nonneg x y, fun x y => ?_⟩
  change w x y ≤ 1
  have entry : w x y ≤ ∑ y', w x y' :=
    Finset.single_le_sum (fun y' _ => nonneg x y') (Finset.mem_univ y)
  rw [rows x] at entry
  exact entry.trans (distribution.le_one x)

theorem isCompact_couplingSet (distribution : IsDistribution μ) : IsCompact (couplingSet μ ν) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_couplingSet μ ν)
    ((Metric.isBounded_Icc 0 1).subset (couplingSet_subset_Icc distribution))

/-- **An optimal coupling exists** on finite spaces. -/
theorem exists_optimal_coupling (first : IsDistribution μ) (second : IsDistribution ν)
    (m : S → T → ℝ) : ∃ ω : Coupling μ ν, ω.cost m = kantorovich m μ ν := by
  have nonempty : (couplingSet μ ν).Nonempty :=
    let ω := Coupling.independent first second
    ⟨ω.weight, ω.nonneg, ω.sum_right, ω.sum_left⟩
  have continuous : ContinuousOn (fun w : S → T → ℝ => ∑ x, ∑ y, w x y * m x y)
      (couplingSet μ ν) :=
    have entry : ∀ (x : S) (y : T), Continuous fun w : S → T → ℝ => w x y := fun x y =>
      (continuous_apply y).comp (continuous_apply x)
    (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      (entry x y).mul continuous_const).continuousOn
  obtain ⟨w, member, minimal⟩ := (isCompact_couplingSet first).exists_isMinOn nonempty continuous
  let ω : Coupling μ ν := ⟨w, member.1, member.2.1, member.2.2⟩
  refine ⟨ω, le_antisymm (le_kantorovich first second fun ω' => ?_) (kantorovich_le first m ω)⟩
  exact isMinOn_iff.mp minimal ω'.weight ⟨ω'.nonneg, ω'.sum_right, ω'.sum_left⟩

end Kantorovich

/-! ## The observation distance and the Kantorovich operator -/

section Operator

variable [Fintype Atom] (P : LabelledMarkovChain ℝ A Atom S) (Q : LabelledMarkovChain ℝ A Atom T)

/-- The observation distance: the largest difference of an observable. -/
noncomputable def observationDistance (s : S) (t : T) : ℝ :=
  observationGap (P.observation s) (Q.observation t)

theorem observationDistance_le_iff {s : S} {t : T} {b : ℝ} :
    observationDistance P Q s t ≤ b ↔ 0 ≤ b ∧ ∀ i, |P.observe i s - Q.observe i t| ≤ b :=
  observationGap_le_iff

theorem observationDistance_nonneg (s : S) (t : T) : 0 ≤ observationDistance P Q s t :=
  ((observationDistance_le_iff P Q).mp le_rfl).1

theorem abs_observe_sub_le_observationDistance (i : Atom) (s : S) (t : T) :
    |P.observe i s - Q.observe i t| ≤ observationDistance P Q s t :=
  ((observationDistance_le_iff P Q).mp le_rfl).2 i

/-- A uniform bound on observation distances. -/
noncomputable def observationBound : ℝ :=
  Finset.univ.fold max 0 fun p : S × T => observationDistance P Q p.1 p.2

theorem observationBound_nonneg : 0 ≤ observationBound P Q := by
  rw [observationBound, Finset.le_fold_max]
  exact Or.inl le_rfl

theorem observationDistance_le_observationBound (s : S) (t : T) :
    observationDistance P Q s t ≤ observationBound P Q := by
  rw [observationBound, Finset.le_fold_max]
  exact Or.inr ⟨(s, t), Finset.mem_univ _, le_rfl⟩

/-- **The constant bound**: at a discount `c ≤ 1`, the largest observation
distance is a coupling bound. -/
theorem couplingBound_const {c : ℝ} (c_le : c ≤ 1) :
    CouplingBound P Q c fun _ _ => observationBound P Q where
  nonneg _ _ := observationBound_nonneg P Q
  observe_le i s t := (abs_observe_sub_le_observationDistance P Q i s t).trans
    (observationDistance_le_observationBound P Q s t)
  step_le a s t := ⟨Coupling.independent (P.isDistribution a s) (Q.isDistribution a t), by
    rw [Coupling.cost_const _ (P.isDistribution a s)]
    nlinarith [observationBound_nonneg P Q]⟩

variable [Fintype A]

/-- **The Kantorovich operator** at discount `c`. -/
noncomputable def kantorovichStep (c : ℝ) (m : S → T → ℝ) (s : S) (t : T) : ℝ :=
  Finset.univ.fold max (observationDistance P Q s t) fun a =>
    c * kantorovich m (P.trans a s) (Q.trans a t)

variable {P Q} {c : ℝ}

theorem kantorovichStep_le_iff {m : S → T → ℝ} {s : S} {t : T} {b : ℝ} :
    kantorovichStep P Q c m s t ≤ b ↔
      observationDistance P Q s t ≤ b ∧ ∀ a, c * kantorovich m (P.trans a s) (Q.trans a t) ≤ b := by
  rw [kantorovichStep, Finset.fold_max_le]
  exact and_congr Iff.rfl ⟨fun all a => all a (Finset.mem_univ a), fun all a _ => all a⟩

theorem observationDistance_le_kantorovichStep (m : S → T → ℝ) (s : S) (t : T) :
    observationDistance P Q s t ≤ kantorovichStep P Q c m s t := by
  rw [kantorovichStep, Finset.le_fold_max]
  exact Or.inl le_rfl

theorem mul_kantorovich_le_kantorovichStep (m : S → T → ℝ) (a : A) (s : S) (t : T) :
    c * kantorovich m (P.trans a s) (Q.trans a t) ≤ kantorovichStep P Q c m s t := by
  rw [kantorovichStep, Finset.le_fold_max]
  exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩

theorem kantorovichStep_mono (c_nonneg : 0 ≤ c) {m m' : S → T → ℝ}
    (le : ∀ x y, m x y ≤ m' x y) (s : S) (t : T) :
    kantorovichStep P Q c m s t ≤ kantorovichStep P Q c m' s t :=
  kantorovichStep_le_iff.mpr ⟨observationDistance_le_kantorovichStep m' s t, fun a =>
    (mul_le_mul_of_nonneg_left
      (kantorovich_mono (P.isDistribution a s) (Q.isDistribution a t) le) c_nonneg).trans
      (mul_kantorovich_le_kantorovichStep m' a s t)⟩

/-- **A coupling bound is exactly a prefixed point of the Kantorovich
operator.** -/
theorem couplingBound_iff_step_le (c_nonneg : 0 ≤ c) {m : S → T → ℝ} :
    CouplingBound P Q c m ↔ ∀ s t, kantorovichStep P Q c m s t ≤ m s t := by
  constructor
  · intro bound s t
    refine kantorovichStep_le_iff.mpr ⟨(observationDistance_le_iff P Q).mpr
      ⟨bound.nonneg s t, fun i => bound.observe_le i s t⟩, fun a => ?_⟩
    obtain ⟨ω, le⟩ := bound.step_le a s t
    exact (mul_le_mul_of_nonneg_left (kantorovich_le (P.isDistribution a s) m ω) c_nonneg).trans le
  · intro prefixed
    have parts := fun s t => kantorovichStep_le_iff.mp (prefixed s t)
    refine ⟨fun s t => (observationDistance_nonneg P Q s t).trans (parts s t).1,
      fun i s t => (abs_observe_sub_le_observationDistance P Q i s t).trans (parts s t).1,
      fun a s t => ?_⟩
    obtain ⟨ω, optimal⟩ :=
      exists_optimal_coupling (P.isDistribution a s) (Q.isDistribution a t) m
    exact ⟨ω, by rw [optimal]; exact (parts s t).2 a⟩

end Operator

/-! ## The iterates and the metric -/

section Metric

variable [Fintype Atom] [Fintype A] (P : LabelledMarkovChain ℝ A Atom S)
  (Q : LabelledMarkovChain ℝ A Atom T)

/-- **The iterates of the Kantorovich operator** from the observation
distance. -/
noncomputable def approxMetric (c : ℝ) : ℕ → S → T → ℝ
  | 0 => observationDistance P Q
  | n + 1 => kantorovichStep P Q c (approxMetric c n)

/-- **The bisimulation metric**: the supremum of the iterates. -/
noncomputable def bisimulationMetric (c : ℝ) (s : S) (t : T) : ℝ :=
  ⨆ n, approxMetric P Q c n s t

variable {P Q} {c : ℝ}

theorem approxMetric_nonneg : ∀ n s t, 0 ≤ approxMetric P Q c n s t
  | 0, s, t => observationDistance_nonneg P Q s t
  | _ + 1, s, t => (observationDistance_nonneg P Q s t).trans
      (observationDistance_le_kantorovichStep _ s t)

theorem approxMetric_le_succ (c_nonneg : 0 ≤ c) :
    ∀ n s t, approxMetric P Q c n s t ≤ approxMetric P Q c (n + 1) s t
  | 0, s, t => observationDistance_le_kantorovichStep _ s t
  | n + 1, s, t => kantorovichStep_mono c_nonneg (approxMetric_le_succ c_nonneg n) s t

theorem approxMetric_mono (c_nonneg : 0 ≤ c) (s : S) (t : T) :
    Monotone fun n => approxMetric P Q c n s t :=
  monotone_nat_of_le_succ fun n => approxMetric_le_succ c_nonneg n s t

/-- **Every coupling bound bounds every iterate.** -/
theorem approxMetric_le {m : S → T → ℝ} (bound : CouplingBound P Q c m) (c_nonneg : 0 ≤ c) :
    ∀ n s t, approxMetric P Q c n s t ≤ m s t
  | 0, s, t => (observationDistance_le_iff P Q).mpr
      ⟨bound.nonneg s t, fun i => bound.observe_le i s t⟩
  | n + 1, s, t => kantorovichStep_le_iff.mpr ⟨(observationDistance_le_iff P Q).mpr
      ⟨bound.nonneg s t, fun i => bound.observe_le i s t⟩, fun a => by
        obtain ⟨ω, le⟩ := bound.step_le a s t
        calc c * kantorovich (approxMetric P Q c n) (P.trans a s) (Q.trans a t)
            ≤ c * ω.cost (approxMetric P Q c n) :=
              mul_le_mul_of_nonneg_left (kantorovich_le (P.isDistribution a s) _ ω) c_nonneg
          _ ≤ c * ω.cost m :=
              mul_le_mul_of_nonneg_left (ω.cost_mono (approxMetric_le bound c_nonneg n)) c_nonneg
          _ ≤ m s t := le⟩

theorem bddAbove_approxMetric (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    BddAbove (Set.range fun n => approxMetric P Q c n s t) :=
  ⟨observationBound P Q, fun _ ⟨n, same⟩ =>
    same ▸ approxMetric_le (couplingBound_const P Q c_le) c_nonneg n s t⟩

theorem approxMetric_le_bisimulationMetric (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (n : ℕ) (s : S)
    (t : T) : approxMetric P Q c n s t ≤ bisimulationMetric P Q c s t :=
  le_ciSup (bddAbove_approxMetric c_nonneg c_le s t) n

theorem bisimulationMetric_nonneg (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    0 ≤ bisimulationMetric P Q c s t :=
  (approxMetric_nonneg 0 s t).trans (approxMetric_le_bisimulationMetric c_nonneg c_le 0 s t)

/-- **The metric lies below every coupling bound.** -/
theorem bisimulationMetric_le {m : S → T → ℝ} (bound : CouplingBound P Q c m) (c_nonneg : 0 ≤ c)
    (s : S) (t : T) : bisimulationMetric P Q c s t ≤ m s t :=
  ciSup_le fun n => approxMetric_le bound c_nonneg n s t

/-- On finitely many pairs the iterates converge uniformly. -/
theorem exists_uniform_approx (c_nonneg : 0 ≤ c) {η : ℝ} (η_pos : 0 < η) :
    ∃ n, ∀ x y, bisimulationMetric P Q c x y ≤ approxMetric P Q c n x y + η := by
  have each : ∀ p : S × T, ∀ᶠ n in atTop,
      bisimulationMetric P Q c p.1 p.2 ≤ approxMetric P Q c n p.1 p.2 + η := by
    intro p
    obtain ⟨N, close⟩ := exists_lt_of_lt_ciSup
      (show bisimulationMetric P Q c p.1 p.2 - η < ⨆ n, approxMetric P Q c n p.1 p.2 by
        change bisimulationMetric P Q c p.1 p.2 - η < bisimulationMetric P Q c p.1 p.2
        linarith)
    exact eventually_atTop.mpr ⟨N, fun n le => by
      linarith [approxMetric_mono (P := P) (Q := Q) c_nonneg p.1 p.2 le]⟩
  obtain ⟨n, all⟩ := (eventually_all.mpr each).exists
  exact ⟨n, fun x y => all (x, y)⟩

theorem mul_kantorovich_bisimulationMetric_le (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (a : A) (s : S)
    (t : T) :
    c * kantorovich (bisimulationMetric P Q c) (P.trans a s) (Q.trans a t) ≤
      bisimulationMetric P Q c s t := by
  apply le_of_forall_pos_le_add
  intro η η_pos
  obtain ⟨n, close⟩ := exists_uniform_approx (P := P) (Q := Q) c_nonneg η_pos
  have lifted := kantorovich_le_add (P.isDistribution a s) (Q.isDistribution a t) close
  calc c * kantorovich (bisimulationMetric P Q c) (P.trans a s) (Q.trans a t)
      ≤ c * (kantorovich (approxMetric P Q c n) (P.trans a s) (Q.trans a t) + η) :=
        mul_le_mul_of_nonneg_left lifted c_nonneg
    _ = c * kantorovich (approxMetric P Q c n) (P.trans a s) (Q.trans a t) + c * η := mul_add _ _ _
    _ ≤ approxMetric P Q c (n + 1) s t + η :=
        add_le_add (mul_kantorovich_le_kantorovichStep _ a s t)
          (mul_le_of_le_one_left η_pos.le c_le)
    _ ≤ bisimulationMetric P Q c s t + η :=
        add_le_add_left (approxMetric_le_bisimulationMetric c_nonneg c_le (n + 1) s t) η

/-- **The metric is a coupling bound**: with the least bounds above, the
least coupling bound. -/
theorem couplingBound_bisimulationMetric (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    CouplingBound P Q c (bisimulationMetric P Q c) where
  nonneg := bisimulationMetric_nonneg c_nonneg c_le
  observe_le i s t := (abs_observe_sub_le_observationDistance P Q i s t).trans
    (approxMetric_le_bisimulationMetric c_nonneg c_le 0 s t)
  step_le a s t := by
    obtain ⟨ω, optimal⟩ := exists_optimal_coupling (P.isDistribution a s) (Q.isDistribution a t)
      (bisimulationMetric P Q c)
    exact ⟨ω, by rw [optimal]; exact mul_kantorovich_bisimulationMetric_le c_nonneg c_le a s t⟩

/-- **The metric is a fixed point of the Kantorovich operator.** -/
theorem bisimulationMetric_eq_step (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    bisimulationMetric P Q c = kantorovichStep P Q c (bisimulationMetric P Q c) := by
  funext s t
  apply le_antisymm
  · refine ciSup_le fun n => ?_
    calc approxMetric P Q c n s t ≤ approxMetric P Q c (n + 1) s t :=
          approxMetric_le_succ c_nonneg n s t
      _ ≤ kantorovichStep P Q c (bisimulationMetric P Q c) s t :=
          kantorovichStep_mono c_nonneg
            (fun x y => approxMetric_le_bisimulationMetric c_nonneg c_le n x y) s t
  · exact kantorovichStep_le_iff.mpr ⟨approxMetric_le_bisimulationMetric c_nonneg c_le 0 s t,
      fun a => mul_kantorovich_bisimulationMetric_le c_nonneg c_le a s t⟩

/-- **The metric is the least prefixed point of the Kantorovich operator.** -/
theorem bisimulationMetric_le_of_step_le (c_nonneg : 0 ≤ c) {m : S → T → ℝ}
    (prefixed : ∀ s t, kantorovichStep P Q c m s t ≤ m s t) (s : S) (t : T) :
    bisimulationMetric P Q c s t ≤ m s t :=
  bisimulationMetric_le ((couplingBound_iff_step_le c_nonneg).mpr prefixed) c_nonneg s t

/-! ### Soundness of the logical characterisation -/

open FunctionalExpression

/-- **Expressions of depth at most `n` vary by at most the `n`-th iterate.** -/
theorem abs_eval_sub_le_approxMetric (c_nonneg : 0 ≤ c) :
    ∀ (φ : FunctionalExpression ℝ A Atom) (n : ℕ), φ.depth ≤ n → ∀ s t,
      |φ.eval P c s - φ.eval Q c t| ≤ approxMetric P Q c n s t
  | .one, n, _, s, t => by
      simp only [eval, sub_self, abs_zero]
      exact approxMetric_nonneg n s t
  | .observe i, n, _, s, t =>
      (abs_observe_sub_le_observationDistance P Q i s t).trans
        (approxMetric_mono c_nonneg s t (Nat.zero_le n))
  | .oneMinus φ, n, deep, s, t => by
      simp only [eval]
      rw [show 1 - φ.eval P c s - (1 - φ.eval Q c t) = -(φ.eval P c s - φ.eval Q c t) by ring,
        abs_neg]
      exact abs_eval_sub_le_approxMetric c_nonneg φ n deep s t
  | .min φ ψ, n, deep, s, t => (abs_min_sub_min_le_max _ _ _ _).trans (max_le
      (abs_eval_sub_le_approxMetric c_nonneg φ n ((le_max_left _ _).trans deep) s t)
      (abs_eval_sub_le_approxMetric c_nonneg ψ n ((le_max_right _ _).trans deep) s t))
  | .max φ ψ, n, deep, s, t => (abs_max_sub_max_le_max _ _ _ _).trans (max_le
      (abs_eval_sub_le_approxMetric c_nonneg φ n ((le_max_left _ _).trans deep) s t)
      (abs_eval_sub_le_approxMetric c_nonneg ψ n ((le_max_right _ _).trans deep) s t))
  | .sub φ q, n, deep, s, t => by
      simp only [eval]
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
      · rw [sub_sub_sub_cancel_right]
        exact abs_eval_sub_le_approxMetric c_nonneg φ n deep s t
      · rw [sub_self, abs_zero]
        exact approxMetric_nonneg n s t
  | .next a φ, n, deep, s, t => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp only [depth] at deep; omega⟩
      have inner : φ.depth ≤ k := by simp only [depth] at deep; omega
      have lifted := abs_expect_sub_le_kantorovich (P.isDistribution a s) (Q.isDistribution a t)
        (abs_eval_sub_le_approxMetric c_nonneg φ k inner)
      simp only [eval]
      rw [← mul_sub, abs_mul, abs_of_nonneg c_nonneg]
      exact (mul_le_mul_of_nonneg_left lifted c_nonneg).trans
        (mul_kantorovich_le_kantorovichStep _ a s t)

/-- **Every functional expression varies by at most the metric.** -/
theorem abs_eval_sub_le_bisimulationMetric (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (φ : FunctionalExpression ℝ A Atom) (s : S) (t : T) :
    |φ.eval P c s - φ.eval Q c t| ≤ bisimulationMetric P Q c s t :=
  (abs_eval_sub_le_approxMetric c_nonneg φ φ.depth le_rfl s t).trans
    (approxMetric_le_bisimulationMetric c_nonneg c_le _ s t)

/-! ### Zero distance and the pseudometric laws -/

/-- **Zero distance is probabilistic bisimilarity.** -/
theorem bisimulationMetric_eq_zero_iff (c_pos : 0 < c) (c_le : c ≤ 1) {s : S} {t : T} :
    bisimulationMetric P Q c s t = 0 ↔ ProbabilisticallyBisimilar P Q s t := by
  constructor
  · intro zero
    exact ⟨_,
      (couplingBound_bisimulationMetric c_pos.le c_le).isProbabilisticBisimulation_zero c_pos, zero⟩
  · rintro ⟨R, bisimulation, related⟩
    classical
    have bound := bisimulation.couplingBound c_pos.le c_le (observationBound_nonneg P Q)
      fun i s t => (abs_observe_sub_le_observationDistance P Q i s t).trans
        (observationDistance_le_observationBound P Q s t)
    have below := bisimulationMetric_le bound c_pos.le s t
    rw [if_pos related] at below
    exact le_antisymm below (bisimulationMetric_nonneg c_pos.le c_le s t)

/-- **The metric vanishes on the diagonal.** -/
theorem bisimulationMetric_self [DecidableEq S] (c_pos : 0 < c) (c_le : c ≤ 1) (s : S) :
    bisimulationMetric P P c s s = 0 :=
  (bisimulationMetric_eq_zero_iff c_pos c_le).mpr ⟨Eq, isProbabilisticBisimulation_eq, rfl⟩

/-- **Symmetry.** -/
theorem bisimulationMetric_comm (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    bisimulationMetric Q P c t s = bisimulationMetric P Q c s t :=
  le_antisymm
    (bisimulationMetric_le (couplingBound_bisimulationMetric c_nonneg c_le).swap c_nonneg t s)
    (bisimulationMetric_le (couplingBound_bisimulationMetric c_nonneg c_le).swap c_nonneg s t)

/-- **The triangle inequality.** -/
theorem bisimulationMetric_triangle (R : LabelledMarkovChain ℝ A Atom U) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) (s : S) (t : T) (u : U) :
    bisimulationMetric P R c s u ≤ bisimulationMetric P Q c s t + bisimulationMetric Q R c t u :=
  haveI : Nonempty T := ⟨t⟩
  (bisimulationMetric_le ((couplingBound_bisimulationMetric c_nonneg c_le).comp
    (couplingBound_bisimulationMetric c_nonneg c_le) c_nonneg) c_nonneg s u).trans
      (infConvolution_le _ _ s t u)

/-! ### Deterministic chains at discount `1`: the Girard–Pappas distance -/

section Deterministic

open Mettapedia.Cybernetics.MindWorldApproximation

variable [DecidableEq S] [DecidableEq T] [Nonempty A] {f : A → S → S} {f' : A → T → T}
  {obs : Atom → S → ℝ} {obs' : Atom → T → ℝ}

/-- **On deterministic chains at discount `1`, the bisimulation metric is the
Girard–Pappas distance**: two states are within `ε` exactly when one
approximate bisimulation at precision `ε`, for every action, relates them. -/
theorem bisimulationMetric_ofFunction_le_iff {s : S} {t : T} {ε : ℝ} :
    bisimulationMetric (LabelledMarkovChain.ofFunction f obs)
        (LabelledMarkovChain.ofFunction f' obs') 1 s t ≤ ε ↔
      ∃ R : S → T → Prop, (∀ a, IsApproxBisimulation observationGap (fun x x' => f a x = x')
        (fun y y' => f' a y = y') (fun x i => obs i x) (fun y i => obs' i y) ε R) ∧ R s t := by
  constructor
  · intro close
    exact ⟨_, fun a => (couplingBound_bisimulationMetric (c := 1) zero_le_one le_rfl
      (P := LabelledMarkovChain.ofFunction f obs)
      (Q := LabelledMarkovChain.ofFunction f' obs')).isApproxBisimulation_ofFunction a ε, close⟩
  · rintro ⟨R, bisimulation, related⟩
    classical
    have ε_nonneg : 0 ≤ ε := (inferInstance : Nonempty A).elim fun a =>
      (observationGap_le_iff.mp ((bisimulation a).1.close related)).1
    set B := max ε (observationBound (LabelledMarkovChain.ofFunction f obs)
      (LabelledMarkovChain.ofFunction f' obs'))
    have bound := couplingBound_of_isApproxBisimulation (c := (1 : ℝ)) bisimulation ε_nonneg
      (le_max_left ε _) (fun i x y => (abs_observe_sub_le_observationDistance
        (LabelledMarkovChain.ofFunction f obs) (LabelledMarkovChain.ofFunction f' obs') i x y).trans
          ((observationDistance_le_observationBound _ _ x y).trans (le_max_right _ _)))
      zero_le_one le_rfl
    have below := bisimulationMetric_le bound zero_le_one s t
    rw [if_pos related] at below
    exact below

end Deterministic

end Metric

end Mettapedia.Cybernetics.ApproximateAdequacy
