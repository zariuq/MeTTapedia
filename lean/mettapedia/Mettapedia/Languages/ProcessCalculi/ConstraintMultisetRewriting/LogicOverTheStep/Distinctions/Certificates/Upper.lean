import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Cast

/-!
# The upper certificate: a checked prefixpoint

A prefixpoint certificate for a finite chain with rational masses (`Prefixpoint`) is a rational
kernel `D` on pairs of states with, for some actions and pairs, a table meant to couple the two
successor distributions. The checker (`check`) decides it in exact rational arithmetic, and its
acceptance is a theorem about the bisimulation metric of the chain read in the reals.

**What is checked.**
* *Soundness conditions* (`coreCheck`): `D ≥ 0`; `|obs i s - obs i t| ≤ D s t` for every
  observation (for an indicator chain: `D ≥ 1` wherever an observation differs,
  `observe_condition_iff`); every action at every pair covered (`coveredAt`): a listed table
  must be a coupling (nonnegative, with the right row and column sums) whose discounted
  expected `D` is at most `D` at the pair.
* *Omitted pairs are filled in by the checker*, each with its justification:
  - the diagonal needs nothing: the proof uses `D` with its diagonal set to zero
    (`offDiagonal`), where the diagonal coupling costs nothing;
  - the reverse of a listed pair takes the reversed table, which is a coupling of the reversed
    pair (`Coupling.swap`), with its cost computed;
  - any other pair takes the independent coupling (`Coupling.independent`), with its cost
    computed.
* *Shape* (`shapeCheck`): `D ≤ 1` and `D` symmetric, the shape of the exact metric for an
  indicator chain at a discount at most one.

**Theorems.**
* `coreCheck_couplingBound`: acceptance of the soundness conditions makes `D`, with its diagonal
  set to zero, a `CouplingBound` of the rational chain at `c`, for `0 ≤ c`.
* `check_sound`: acceptance implies `bisimulationMetric ≤ D` pointwise on the real chain, for
  every discount `0 ≤ c`, which is the range `bisimulationMetric_le` needs; `check_sound_of_eq` for
  a real chain given with the same masses.

**The shape is classified, not needed.** Soundness uses only the core conditions
(`coreCheck_sound`). The shape loses no bound: from any coupling bound of a chain with itself,
the symmetric minimum and the minimum with one are coupling bounds below it
(`couplingBound_min_swap`, `couplingBound_min_one`, the latter for observation differences at
most one and `c ≤ 1`). Under the shape the fill-ins of the reverse pairs and of the pairs at
kernel one never fail (`coveredAt_reverse`, `coveredAt_of_one_le`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Mettapedia.Cybernetics.ApproximateAdequacy

/-! ## Tables -/

section Tables

variable {S : Type*} [Fintype S]

/-- The expected value of `D` under a joint weighting `θ`. -/
def jointCost (θ D : S → S → ℚ) : ℚ :=
  ∑ u, ∑ v, θ u v * D u v

/-- **A table couples `μ` and `ν`**: it is nonnegative, with row sums `μ` and column sums `ν`. -/
def IsCouplingTable (μ ν : S → ℚ) (θ : S → S → ℚ) : Prop :=
  (∀ u v, 0 ≤ θ u v) ∧ (∀ u, ∑ v, θ u v = μ u) ∧ ∀ v, ∑ u, θ u v = ν v

instance (μ ν : S → ℚ) (θ : S → S → ℚ) : Decidable (IsCouplingTable μ ν θ) := by
  unfold IsCouplingTable
  infer_instance

/-- The coupling given by a table that couples. -/
def IsCouplingTable.coupling {μ ν : S → ℚ} {θ : S → S → ℚ} (table : IsCouplingTable μ ν θ) :
    Coupling μ ν :=
  ⟨θ, table.1, table.2.1, table.2.2⟩

/-- The reversed table. -/
def reverseTable (θ : S → S → ℚ) : S → S → ℚ :=
  fun u v => θ v u

/-- The independent table of two weightings. -/
def productTable (μ ν : S → ℚ) : S → S → ℚ :=
  fun u v => μ u * ν v

/-- The kernel with its diagonal set to zero. -/
def offDiagonal [DecidableEq S] (D : S → S → ℚ) : S → S → ℚ :=
  fun s t => if s = t then 0 else D s t

end Tables

/-! ## Certificates and the checker -/

/-- **A prefixpoint certificate** for a chain with actions `A` on states `S`: a rational kernel on
pairs of states, and, for some actions and pairs, a table coupling the two successor
distributions. A pair left at `none` is filled in by the checker. -/
structure Prefixpoint (A S : Type*) where
  /-- The kernel claimed to bound the metric. -/
  kernel : S → S → ℚ
  /-- The listed couplings. -/
  listed : A → S → S → Option (S → S → ℚ)

variable {A Atom S : Type*} [Fintype S] [DecidableEq S]

section Checker

variable (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : Prefixpoint A S)

/-- **One action at one pair, from a cost kernel to a bound kernel.** A listed table must couple the
two successor distributions, with discounted cost under `cost` at most `bound` at the pair. An
omitted pair is filled in: the diagonal needs nothing; otherwise the reversed table of the reverse
pair, if that pair is listed, or the independent coupling, each with its discounted cost computed. -/
def coveredBetween (cost bound : S → S → ℚ) (listed : A → S → S → Option (S → S → ℚ)) (a : A)
    (s t : S) : Bool :=
  match listed a s t with
  | some θ =>
      decide (IsCouplingTable (P.trans a s) (P.trans a t) θ) &&
        decide (c * jointCost θ cost ≤ bound s t)
  | none =>
      decide (s = t) ||
        (match listed a t s with
          | some θ => decide (c * jointCost (reverseTable θ) cost ≤ bound s t)
          | none => false) ||
        decide (c * jointCost (productTable (P.trans a s) (P.trans a t)) cost ≤ bound s t)

/-- **One action at one pair of a prefixpoint**: from the kernel to itself. -/
def coveredAt (a : A) (s t : S) : Bool :=
  coveredBetween P c cert.kernel cert.kernel cert.listed a s t

/-- **The conditions soundness needs**: a nonnegative kernel bounding every difference of an
observation, with every action at every pair covered. -/
def coreCheck [Fintype A] [Fintype Atom] : Bool :=
  decide (∀ s t, 0 ≤ cert.kernel s t) &&
    decide (∀ i s t, |P.observe i s - P.observe i t| ≤ cert.kernel s t) &&
    decide (∀ a s t, coveredAt P c cert a s t = true)

/-- **The shape of the format**: the kernel is at most one and symmetric. -/
def shapeCheck : Bool :=
  decide (∀ s t, cert.kernel s t ≤ 1) && decide (∀ s t, cert.kernel s t = cert.kernel t s)

/-- **The checker** of prefixpoint certificates. -/
def check [Fintype A] [Fintype Atom] : Bool :=
  coreCheck P c cert && shapeCheck cert

end Checker

/-! ## Soundness -/

section Covered

variable {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cert : Prefixpoint A S}

omit [Fintype S] in
theorem offDiagonal_le (nonneg : ∀ s t, 0 ≤ cert.kernel s t) (s t : S) :
    offDiagonal cert.kernel s t ≤ cert.kernel s t := by
  unfold offDiagonal
  split_ifs with same
  · subst same
    exact nonneg s s
  · exact le_rfl

/-- **A covered pair has its coupling**: if every action at every pair is covered from `cost` to
`bound`, then for every action and pair of distinct states some coupling of the successor
distributions has discounted cost under `cost` at most `bound` at the pair. -/
theorem exists_coupling_of_coveredBetween {cost bound : S → S → ℚ}
    {listed : A → S → S → Option (S → S → ℚ)}
    (covered : ∀ a s t, coveredBetween P c cost bound listed a s t = true)
    (a : A) {s t : S} (distinct : s ≠ t) :
    ∃ ω : Coupling (P.trans a s) (P.trans a t), c * ω.cost cost ≤ bound s t := by
  have here := covered a s t
  rcases hit : listed a s t with _ | θ
  · simp only [coveredBetween, hit, Bool.or_eq_true, decide_eq_true_eq] at here
    rcases here with (equal | reverse) | product
    · exact absurd equal distinct
    · rcases reversed : listed a t s with _ | θ
      · simp [reversed] at reverse
      · simp only [reversed, decide_eq_true_eq] at reverse
        have there := covered a t s
        simp only [coveredBetween, reversed, Bool.and_eq_true, decide_eq_true_eq] at there
        exact ⟨there.1.coupling.swap, reverse⟩
    · exact ⟨Coupling.independent (P.isDistribution a s) (P.isDistribution a t), product⟩
  · simp only [coveredBetween, hit, Bool.and_eq_true, decide_eq_true_eq] at here
    exact ⟨here.1.coupling, here.2⟩

/-- **A covered pair of a prefixpoint has its coupling.** -/
theorem exists_coupling_of_covered (covered : ∀ a s t, coveredAt P c cert a s t = true)
    (a : A) {s t : S} (distinct : s ≠ t) :
    ∃ ω : Coupling (P.trans a s) (P.trans a t), c * ω.cost cert.kernel ≤ cert.kernel s t :=
  exists_coupling_of_coveredBetween covered a distinct

end Covered

section Soundness

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ}
  {cert : Prefixpoint A S}

theorem coreCheck_iff :
    coreCheck P c cert = true ↔
      (∀ s t, 0 ≤ cert.kernel s t) ∧
        (∀ i s t, |P.observe i s - P.observe i t| ≤ cert.kernel s t) ∧
          ∀ a s t, coveredAt P c cert a s t = true := by
  simp only [coreCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem check_iff :
    check P c cert = true ↔ coreCheck P c cert = true ∧
      (∀ s t, cert.kernel s t ≤ 1) ∧ ∀ s t, cert.kernel s t = cert.kernel t s := by
  simp only [check, shapeCheck, Bool.and_eq_true, decide_eq_true_eq]

/-- **The soundness conditions give a coupling bound**: the kernel with its diagonal set to zero
is a coupling bound of the rational chain with itself, at every discount `0 ≤ c`. -/
theorem coreCheck_couplingBound (accepted : coreCheck P c cert = true) (c_nonneg : 0 ≤ c) :
    CouplingBound P P c (offDiagonal cert.kernel) := by
  obtain ⟨nonneg, observed, covered⟩ := coreCheck_iff.mp accepted
  refine ⟨fun s t => ?_, fun i s t => ?_, fun a s t => ?_⟩
  · unfold offDiagonal
    split_ifs
    · exact le_rfl
    · exact nonneg s t
  · unfold offDiagonal
    split_ifs with same
    · subst same
      simp
    · exact observed i s t
  · by_cases same : s = t
    · subst same
      refine ⟨Coupling.diagonal (P.isDistribution a s), ?_⟩
      have zero : (Coupling.diagonal (P.isDistribution a s)).cost (offDiagonal cert.kernel) = 0 := by
        unfold Coupling.cost
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        change (if x = y then P.trans a s x else 0) * (if x = y then 0 else cert.kernel x y) = 0
        split_ifs <;> simp
      rw [zero, mul_zero]
      simp [offDiagonal]
    · obtain ⟨ω, le⟩ := exists_coupling_of_covered covered a same
      refine ⟨ω, ?_⟩
      rw [show offDiagonal cert.kernel s t = cert.kernel s t by simp [offDiagonal, same]]
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono (offDiagonal_le nonneg)) c_nonneg).trans le

/-- **Soundness of the core conditions**: the bisimulation metric of the real chain is at most the
kernel, at every discount `0 ≤ c`. -/
theorem coreCheck_sound (accepted : coreCheck P c cert = true) (c_nonneg : 0 ≤ c) (s t : S) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t ≤ (cert.kernel s t : ℝ) :=
  (bisimulationMetric_le_real (coreCheck_couplingBound accepted c_nonneg) c_nonneg s t).trans
    (Rat.cast_le.mpr (offDiagonal_le (coreCheck_iff.mp accepted).1 s t))

/-- **Soundness of the checker**: acceptance implies `bisimulationMetric ≤ D` pointwise on the real
chain, at every discount `0 ≤ c`. -/
theorem check_sound (accepted : check P c cert = true) (c_nonneg : 0 ≤ c) (s t : S) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t ≤ (cert.kernel s t : ℝ) :=
  coreCheck_sound (check_iff.mp accepted).1 c_nonneg s t

/-- **The same for a real chain given with the rational masses and observations.** -/
theorem check_sound_of_eq {R : LabelledMarkovChain ℝ A Atom S}
    (trans_eq : ∀ a s x, R.trans a s x = (P.trans a s x : ℝ))
    (observe_eq : ∀ i s, R.observe i s = (P.observe i s : ℝ))
    (accepted : check P c cert = true) (c_nonneg : 0 ≤ c) (s t : S) :
    bisimulationMetric R R (c : ℝ) s t ≤ (cert.kernel s t : ℝ) := by
  obtain rfl := eq_realChain trans_eq observe_eq
  exact check_sound accepted c_nonneg s t

end Soundness

/-! ## Indicator observations -/

omit [DecidableEq S] in
/-- **For an indicator chain the observation condition reads "at least one wherever an observation
differs"**, for a nonnegative kernel. -/
theorem observe_condition_iff {P : LabelledMarkovChain ℚ A Atom S}
    (indicator : ∀ i s, P.observe i s = 0 ∨ P.observe i s = 1) {D : S → S → ℚ}
    (nonneg : ∀ s t, 0 ≤ D s t) :
    (∀ i s t, |P.observe i s - P.observe i t| ≤ D s t) ↔
      ∀ i s t, P.observe i s ≠ P.observe i t → 1 ≤ D s t := by
  constructor
  · intro bounded i s t differs
    have gap := bounded i s t
    rcases indicator i s with first | first <;> rcases indicator i t with second | second <;>
      rw [first, second] at differs gap
    · exact absurd rfl differs
    · norm_num at gap
      exact gap
    · norm_num at gap
      exact gap
    · exact absurd rfl differs
  · intro differs i s t
    have nonneg' := nonneg s t
    by_cases same : P.observe i s = P.observe i t
    · rw [same, sub_self, abs_zero]
      exact nonneg'
    · have far := differs i s t same
      rcases indicator i s with first | first <;> rcases indicator i t with second | second <;>
        rw [first, second] <;> norm_num <;> linarith

/-! ## The shape: what it guarantees, and what it costs -/

section Shape

variable {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cert : Prefixpoint A S}

/-- **Under symmetry the reverse of a listed pair is always filled in.** -/
theorem coveredAt_reverse (symmetric : ∀ u v, cert.kernel u v = cert.kernel v u) {a : A} {s t : S}
    (omitted : cert.listed a s t = none) {θ : S → S → ℚ} (reversed : cert.listed a t s = some θ)
    (there : coveredAt P c cert a t s = true) : coveredAt P c cert a s t = true := by
  simp only [coveredAt, coveredBetween, reversed, Bool.and_eq_true, decide_eq_true_eq] at there
  have same_cost : jointCost (reverseTable θ) cert.kernel = jointCost θ cert.kernel := by
    unfold jointCost reverseTable
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [symmetric v u]
  simp only [coveredAt, coveredBetween, omitted, reversed, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (Or.inr (by rw [same_cost, symmetric s t]; exact there.2))

/-- **Under the bound by one, at a discount at most one, a pair at kernel one is always filled in**
by the independent coupling; for an indicator chain these include the pairs where an observation
differs (`observe_condition_iff`). -/
theorem coveredAt_of_one_le (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (bounded : ∀ u v, cert.kernel u v ≤ 1) {a : A} {s t : S}
    (omitted : cert.listed a s t = none) (far : 1 ≤ cert.kernel s t) :
    coveredAt P c cert a s t = true := by
  simp only [coveredAt, coveredBetween, omitted, Bool.or_eq_true, decide_eq_true_eq]
  refine Or.inr ?_
  have cost_le : jointCost (productTable (P.trans a s) (P.trans a t)) cert.kernel ≤ 1 :=
    (Coupling.independent (P.isDistribution a s) (P.isDistribution a t)).cost_le_of_le
      (P.isDistribution a s) bounded
  calc c * jointCost (productTable (P.trans a s) (P.trans a t)) cert.kernel ≤ c * 1 :=
        mul_le_mul_of_nonneg_left cost_le c_nonneg
    _ ≤ 1 := by linarith
    _ ≤ cert.kernel s t := far

end Shape

section Lossless

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {P : LabelledMarkovChain 𝕜 A Atom S} {c : 𝕜} {m : S → S → 𝕜}

omit [DecidableEq S] in
/-- **Symmetry loses no bound**: the symmetric minimum of a coupling bound of a chain with itself
is a coupling bound. -/
theorem couplingBound_min_swap (bound : CouplingBound P P c m) (c_nonneg : 0 ≤ c) :
    CouplingBound P P c fun s t => min (m s t) (m t s) where
  nonneg s t := le_min (bound.nonneg s t) (bound.nonneg t s)
  observe_le i s t := le_min (bound.observe_le i s t)
    (by rw [abs_sub_comm]; exact bound.observe_le i t s)
  step_le a s t := by
    by_cases order : m s t ≤ m t s
    · obtain ⟨ω, le⟩ := bound.step_le a s t
      refine ⟨ω, ?_⟩
      rw [min_eq_left order]
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono fun x y => min_le_left _ _) c_nonneg).trans le
    · obtain ⟨ω, le⟩ := bound.step_le a t s
      refine ⟨ω.swap, ?_⟩
      rw [min_eq_right (le_of_lt (not_le.mp order))]
      have symmetric : (fun x y => min (m x y) (m y x)) = fun y x => min (m x y) (m y x) :=
        funext fun x => funext fun y => min_comm _ _
      rw [symmetric, ω.cost_swap]
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono fun x y => min_le_left _ _) c_nonneg).trans le

omit [DecidableEq S] in
/-- **The bound by one loses no bound** when every observation difference is at most one and the
discount is at most one. -/
theorem couplingBound_min_one (bound : CouplingBound P P c m) (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (observe_le_one : ∀ i s t, |P.observe i s - P.observe i t| ≤ 1) :
    CouplingBound P P c fun s t => min (m s t) 1 where
  nonneg s t := le_min (bound.nonneg s t) zero_le_one
  observe_le i s t := le_min (bound.observe_le i s t) (observe_le_one i s t)
  step_le a s t := by
    by_cases order : m s t ≤ 1
    · obtain ⟨ω, le⟩ := bound.step_le a s t
      refine ⟨ω, ?_⟩
      rw [min_eq_left order]
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono fun x y => min_le_left _ _) c_nonneg).trans le
    · refine ⟨Coupling.independent (P.isDistribution a s) (P.isDistribution a t), ?_⟩
      rw [min_eq_right (le_of_lt (not_le.mp order))]
      have cost_le := (Coupling.independent (P.isDistribution a s) (P.isDistribution a t)).cost_le_of_le
        (P.isDistribution a s) (m := fun x y => min (m x y) 1) (B := 1) fun x y => min_le_right _ _
      calc c * _ ≤ c * 1 := mul_le_mul_of_nonneg_left cost_le c_nonneg
        _ ≤ 1 := by rw [mul_one]; exact c_le

end Lossless

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
