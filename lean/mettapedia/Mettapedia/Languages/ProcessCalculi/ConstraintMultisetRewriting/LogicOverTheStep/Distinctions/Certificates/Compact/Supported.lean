import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Scaling

/-!
# Certificates read on supports

The prefixpoint checker reads every listed table, and computes every joint cost, over all `n²` pairs
of successors, although a coupling of two distributions vanishes outside the product of their
supports. A **supported certificate** (`Supported`) is a prefixpoint certificate together with, for
every action and state, a set of states containing every successor of positive mass. Its checker
(`supportedCheck`) checks those sets once, against the chain, then reads tables and computes costs only
on products of supports (`supportedCovered`): a listed table is checked as a coupling of the two
distributions restricted to the supports (`IsSupportedTable`), and the reversed and independent
fill-ins are costed there.

**Soundness** (`supportedCheck_sound`): acceptance implies `metric ≤ kernel` at every discount `0 ≤ c`.
The table read on the supports, and zero elsewhere (`restrictTable`), is a coupling of the full
distributions (`IsSupportedTable.isCouplingTable`) with the same cost (`jointCost_restrictTable`); the
independent coupling costs what it costs on the supports (`jointCost_product_supported`). So acceptance
gives the tree's coupling bound, as for the incumbent.

**Work** (`supportedWork`): checking the supports costs one comparison per action, state and successor
and at most one test per element of the support for each successor of positive mass; each pair then
costs a constant number of operations per pair of support elements, instead of per pair of states. As
for every certificate in this folder, reading the certificate's own data (its kernel, tables and
supports) is not counted; the checker's arithmetic and tests are.

**For every chain with small supports** (`supportedWork_all_le`): with supports of at most `σ` states,
the check costs at most `|A| n² (1 + σ) + 3n² + 4 |Atom| n² + |A| n² (5σ² + 3σ + 5)`, quadratic in `n`;
when four times this is at most the incumbent's quartic lower bound, the supported check costs at most a
quarter of every accepted prefixpoint certificate's (`supported_four_times_cheaper_of_large`); with one
action, one observation and supports of at most two states, from ten states on
(`two_successors_from_ten`). No class structure is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S : Type*} [Fintype S] [DecidableEq S]

/-! ## Tables read on supports -/

/-- The joint cost over two sets of states. -/
def supportedCost (U V : Finset S) (θ D : S → S → ℚ) : ℚ :=
  ∑ u ∈ U, ∑ v ∈ V, θ u v * D u v

/-- **A table couples two weightings on two sets of states.** -/
def IsSupportedTable (U V : Finset S) (μ ν : S → ℚ) (θ : S → S → ℚ) : Prop :=
  (∀ u ∈ U, ∀ v ∈ V, 0 ≤ θ u v) ∧ (∀ u ∈ U, ∑ v ∈ V, θ u v = μ u) ∧ ∀ v ∈ V, ∑ u ∈ U, θ u v = ν v

omit [Fintype S] in
instance (U V : Finset S) (μ ν : S → ℚ) (θ : S → S → ℚ) : Decidable (IsSupportedTable U V μ ν θ) := by
  unfold IsSupportedTable
  infer_instance

omit [Fintype S] in
/-- A table read on two sets of states, and zero elsewhere. -/
def restrictTable (U V : Finset S) (θ : S → S → ℚ) : S → S → ℚ :=
  fun u v => if u ∈ U ∧ v ∈ V then θ u v else 0

/-- **A table that couples on the supports is, read there, a coupling of the full distributions**, when
the sets contain every point of positive mass. -/
theorem IsSupportedTable.isCouplingTable {U V : Finset S} {μ ν : S → ℚ} {θ : S → S → ℚ}
    (table : IsSupportedTable U V μ ν θ) (inU : ∀ x, μ x ≠ 0 → x ∈ U)
    (inV : ∀ x, ν x ≠ 0 → x ∈ V) : IsCouplingTable μ ν (restrictTable U V θ) := by
  obtain ⟨nonneg, rows, columns⟩ := table
  refine ⟨fun u v => ?_, fun u => ?_, fun v => ?_⟩
  · unfold restrictTable
    split_ifs with both
    · exact nonneg u both.1 v both.2
    · exact le_rfl
  · by_cases hu : u ∈ U
    · have row : ∑ v, restrictTable U V θ u v = ∑ v ∈ V, θ u v := by
        simp only [restrictTable, hu, true_and]
        exact Fintype.sum_ite_mem V (θ u)
      rw [row, rows u hu]
    · have zero : μ u = 0 := by
        by_contra positive
        exact hu (inU u positive)
      simp [restrictTable, hu, zero]
  · by_cases hv : v ∈ V
    · have column : ∑ u, restrictTable U V θ u v = ∑ u ∈ U, θ u v := by
        simp only [restrictTable, hv, and_true]
        exact Fintype.sum_ite_mem U (fun u => θ u v)
      rw [column, columns v hv]
    · have zero : ν v = 0 := by
        by_contra positive
        exact hv (inV v positive)
      simp [restrictTable, hv, zero]

/-- **The table read on the supports costs its cost on the supports.** -/
theorem jointCost_restrictTable (U V : Finset S) (θ D : S → S → ℚ) :
    jointCost (restrictTable U V θ) D = supportedCost U V θ D := by
  unfold jointCost supportedCost restrictTable
  have each : ∀ u, ∑ v, (if u ∈ U ∧ v ∈ V then θ u v else 0) * D u v =
      if u ∈ U then ∑ v ∈ V, θ u v * D u v else 0 := by
    intro u
    by_cases hu : u ∈ U
    · simp only [hu, true_and, if_true, ite_mul, zero_mul]
      exact Fintype.sum_ite_mem V (fun v => θ u v * D u v)
    · simp [hu]
  simp only [each]
  exact Fintype.sum_ite_mem U (fun u => ∑ v ∈ V, θ u v * D u v)

/-- **The independent coupling costs what it costs on the supports.** -/
theorem jointCost_product_supported {U V : Finset S} {μ ν : S → ℚ} (inU : ∀ x, μ x ≠ 0 → x ∈ U)
    (inV : ∀ x, ν x ≠ 0 → x ∈ V) (D : S → S → ℚ) :
    jointCost (productTable μ ν) D = supportedCost U V (productTable μ ν) D := by
  rw [← jointCost_restrictTable]
  unfold jointCost
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  unfold restrictTable productTable
  split_ifs with both
  · rfl
  · rcases not_and_or.mp both with outU | outV
    · have zero : μ u = 0 := by
        by_contra positive
        exact outU (inU u positive)
      simp [zero]
    · have zero : ν v = 0 := by
        by_contra positive
        exact outV (inV v positive)
      simp [zero]

/-! ## The certificate and its checker -/

/-- **A supported certificate**: a prefixpoint certificate, and for every action and state a set of
states meant to contain every successor of positive mass. -/
structure Supported (A S : Type*) where
  /-- The prefixpoint certificate. -/
  cert : Prefixpoint A S
  /-- The supports. -/
  support : A → S → Finset S

/-- **One action at one pair, read on the supports.** As `coveredAt`, with tables read and costs
computed on the product of the two supports. -/
def supportedCovered (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (sup : Supported A S) (a : A)
    (s t : S) : Bool :=
  match sup.cert.listed a s t with
  | some θ =>
      decide (IsSupportedTable (sup.support a s) (sup.support a t) (P.trans a s) (P.trans a t) θ) &&
        decide (c * supportedCost (sup.support a s) (sup.support a t) θ sup.cert.kernel ≤
          sup.cert.kernel s t)
  | none =>
      decide (s = t) ||
        (match sup.cert.listed a t s with
          | some θ => decide (c * supportedCost (sup.support a s) (sup.support a t) (reverseTable θ)
              sup.cert.kernel ≤ sup.cert.kernel s t)
          | none => false) ||
        decide (c * supportedCost (sup.support a s) (sup.support a t)
          (productTable (P.trans a s) (P.trans a t)) sup.cert.kernel ≤ sup.cert.kernel s t)

/-- **The checker** of supported certificates: the supports against the chain, the kernel's signs,
every observation difference, every action at every pair read on the supports, and the shape. -/
def supportedCheck [Fintype A] [Fintype Atom] (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (sup : Supported A S) : Bool :=
  decide (∀ a s x, P.trans a s x ≠ 0 → x ∈ sup.support a s) &&
    decide (∀ s t, 0 ≤ sup.cert.kernel s t) &&
    decide (∀ i s t, |P.observe i s - P.observe i t| ≤ sup.cert.kernel s t) &&
    decide (∀ a s t, supportedCovered P c sup a s t = true) && shapeCheck sup.cert

/-! ## Soundness -/

section Soundness

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {sup : Supported A S}

theorem supportedCheck_iff :
    supportedCheck P c sup = true ↔
      (∀ a s x, P.trans a s x ≠ 0 → x ∈ sup.support a s) ∧ (∀ s t, 0 ≤ sup.cert.kernel s t) ∧
        (∀ i s t, |P.observe i s - P.observe i t| ≤ sup.cert.kernel s t) ∧
        (∀ a s t, supportedCovered P c sup a s t = true) ∧ shapeCheck sup.cert = true := by
  simp only [supportedCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- **Acceptance gives a coupling bound**: the kernel with its diagonal set to zero, at every discount
`0 ≤ c`. -/
theorem supportedCheck_couplingBound (accepted : supportedCheck P c sup = true) (c_nonneg : 0 ≤ c) :
    CouplingBound P P c (offDiagonal sup.cert.kernel) := by
  obtain ⟨supports, nonneg, observed, covered, _⟩ := supportedCheck_iff.mp accepted
  have exists_coupling : ∀ a s t, s ≠ t →
      ∃ ω : Coupling (P.trans a s) (P.trans a t), c * ω.cost sup.cert.kernel ≤ sup.cert.kernel s t := by
    intro a s t distinct
    have here := covered a s t
    rcases hit : sup.cert.listed a s t with _ | θ
    · simp only [supportedCovered, hit, Bool.or_eq_true, decide_eq_true_eq] at here
      rcases here with (equal | reverse) | product
      · exact absurd equal distinct
      · rcases reversed : sup.cert.listed a t s with _ | θ
        · simp [reversed] at reverse
        · simp only [reversed, decide_eq_true_eq] at reverse
          have there := covered a t s
          simp only [supportedCovered, reversed, Bool.and_eq_true, decide_eq_true_eq] at there
          have table := there.1.isCouplingTable (supports a t) (supports a s)
          refine ⟨table.coupling.swap, ?_⟩
          have cost : table.coupling.swap.cost sup.cert.kernel =
              supportedCost (sup.support a s) (sup.support a t) (reverseTable θ) sup.cert.kernel := by
            unfold Coupling.cost Coupling.swap IsCouplingTable.coupling
            change ∑ u, ∑ v, restrictTable (sup.support a t) (sup.support a s) θ v u *
              sup.cert.kernel u v = _
            have flipped : (fun u v => restrictTable (sup.support a t) (sup.support a s) θ v u) =
                restrictTable (sup.support a s) (sup.support a t) (reverseTable θ) := by
              funext u v
              unfold restrictTable reverseTable
              by_cases hu : u ∈ sup.support a s <;> by_cases hv : v ∈ sup.support a t <;> simp [hu, hv]
            have rewritten : ∑ u, ∑ v, restrictTable (sup.support a t) (sup.support a s) θ v u *
                sup.cert.kernel u v = jointCost (restrictTable (sup.support a s) (sup.support a t)
                  (reverseTable θ)) sup.cert.kernel := by
              unfold jointCost
              rw [← flipped]
            rw [rewritten, jointCost_restrictTable]
          rw [cost]
          exact reverse
      · refine ⟨Coupling.independent (P.isDistribution a s) (P.isDistribution a t), ?_⟩
        have cost : (Coupling.independent (P.isDistribution a s) (P.isDistribution a t)).cost
            sup.cert.kernel = jointCost (productTable (P.trans a s) (P.trans a t)) sup.cert.kernel := rfl
        rw [cost, jointCost_product_supported (supports a s) (supports a t)]
        exact product
    · simp only [supportedCovered, hit, Bool.and_eq_true, decide_eq_true_eq] at here
      have table := here.1.isCouplingTable (supports a s) (supports a t)
      refine ⟨table.coupling, ?_⟩
      have cost : table.coupling.cost sup.cert.kernel =
          jointCost (restrictTable (sup.support a s) (sup.support a t) θ) sup.cert.kernel := rfl
      rw [cost, jointCost_restrictTable]
      exact here.2
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
      have zero : (Coupling.diagonal (P.isDistribution a s)).cost (offDiagonal sup.cert.kernel) = 0 := by
        unfold Coupling.cost
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        change (if x = y then P.trans a s x else 0) * (if x = y then 0 else sup.cert.kernel x y) = 0
        split_ifs <;> simp
      rw [zero, mul_zero]
      simp [offDiagonal]
    · obtain ⟨ω, le⟩ := exists_coupling a s t same
      refine ⟨ω, ?_⟩
      rw [show offDiagonal sup.cert.kernel s t = sup.cert.kernel s t by simp [offDiagonal, same]]
      have below : ∀ u v, offDiagonal sup.cert.kernel u v ≤ sup.cert.kernel u v := fun u v => by
        unfold offDiagonal
        split_ifs with equal
        · subst equal
          exact nonneg u u
        · exact le_rfl
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono below) c_nonneg).trans le

/-- **Soundness**: acceptance implies that the bisimulation metric of the real chain is at most the
kernel, at every discount `0 ≤ c`. -/
theorem supportedCheck_sound (accepted : supportedCheck P c sup = true) (c_nonneg : 0 ≤ c) (s t : S) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t ≤ (sup.cert.kernel s t : ℝ) := by
  refine (bisimulationMetric_le_real (supportedCheck_couplingBound accepted c_nonneg) c_nonneg s t).trans
    (Rat.cast_le.mpr ?_)
  unfold offDiagonal
  split_ifs with same
  · subst same
    exact (supportedCheck_iff.mp accepted).2.1 s s
  · exact le_rfl

end Soundness

/-! ## Counted work -/

/-- `IsSupportedTable U V μ ν θ` over supports of sizes `σ` and `τ`, when it holds. -/
def supportedTableWork (σ τ : ℕ) : Work := (0, 2 * (σ * τ), σ * τ + σ + τ, 0)

/-- `supportedCost U V θ D` over supports of sizes `σ` and `τ`. -/
def supportedJointWork (σ τ : ℕ) : Work := (σ * τ, σ * τ + σ, 0, 0)

/-- `supportedCost U V (productTable μ ν) D`: two products per term. -/
def supportedProductWork (σ τ : ℕ) : Work := (2 * (σ * τ), σ * τ + σ, 0, 0)

/-- **The work of one action at one pair**, following `supportedCovered`. -/
def supportedCoveredWork (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (sup : Supported A S) (a : A)
    (s t : S) : Work :=
  match sup.cert.listed a s t with
  | some θ =>
      if IsSupportedTable (sup.support a s) (sup.support a t) (P.trans a s) (P.trans a t) θ then
        supportedTableWork (sup.support a s).card (sup.support a t).card +
          supportedJointWork (sup.support a s).card (sup.support a t).card + stepWork
      else supportedTableWork (sup.support a s).card (sup.support a t).card
  | none =>
      testWork +
        if s = t then 0
        else
          match sup.cert.listed a t s with
          | some θ =>
              supportedJointWork (sup.support a s).card (sup.support a t).card + stepWork +
                if c * supportedCost (sup.support a s) (sup.support a t) (reverseTable θ)
                    sup.cert.kernel ≤ sup.cert.kernel s t then 0
                else supportedProductWork (sup.support a s).card (sup.support a t).card + stepWork
          | none => supportedProductWork (sup.support a s).card (sup.support a t).card + stepWork

/-- **The work of the support check**: per action, state and successor one comparison, and for a
successor of positive mass at most one test per element of the support. -/
def supportCheckWork [Fintype A] (P : LabelledMarkovChain ℚ A Atom S) (sup : Supported A S) : Work :=
  ∑ a, ∑ s, ∑ x, ((0, 0, 1, if P.trans a s x ≠ 0 then (sup.support a s).card else 0) : Work)

/-- **The work of the checker** `supportedCheck`. -/
def supportedWork [Fintype A] [Fintype Atom] (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (sup : Supported A S) : Work :=
  supportCheckWork P sup + (0, 0, Fintype.card S * Fintype.card S, 0) +
    (0, 2 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)),
      2 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)), 0) +
    ∑ a, ∑ s, ∑ t, supportedCoveredWork P c sup a s t +
    (0, 0, 2 * (Fintype.card S * Fintype.card S), 0)

/-! ## Where it wins, for every chain with small supports -/

/-- **One action at one pair costs at most `5σ² + 3σ + 5`** counted operations when both supports have
at most `σ` states. -/
theorem supportedCoveredWork_all_le (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (sup : Supported A S)
    (a : A) (s t : S) {σ : ℕ} (small_s : (sup.support a s).card ≤ σ)
    (small_t : (sup.support a t).card ≤ σ) :
    (supportedCoveredWork P c sup a s t).all ≤ 5 * (σ * σ) + 3 * σ + 5 := by
  have product : (sup.support a s).card * (sup.support a t).card ≤ σ * σ :=
    Nat.mul_le_mul small_s small_t
  unfold supportedCoveredWork
  rcases sup.cert.listed a s t with _ | θ
  · dsimp only
    split_ifs
    · simp only [Work.all, testWork, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
      omega
    · rcases sup.cert.listed a t s with _ | θ'
      · simp only [Work.all, testWork, supportedProductWork, stepWork, Prod.fst_add, Prod.snd_add]
        omega
      · dsimp only
        split_ifs
        · simp only [Work.all, testWork, supportedJointWork, stepWork, Prod.fst_add, Prod.snd_add,
            Prod.fst_zero, Prod.snd_zero]
          omega
        · simp only [Work.all, testWork, supportedJointWork, supportedProductWork, stepWork,
            Prod.fst_add, Prod.snd_add]
          omega
  · dsimp only
    split_ifs
    · simp only [Work.all, supportedTableWork, supportedJointWork, stepWork, Prod.fst_add,
        Prod.snd_add]
      omega
    · simp only [Work.all, supportedTableWork]
      omega

/-- **Checking a supported certificate whose supports have at most `σ` states costs at most**
`|A| n² (1 + σ) + 3n² + 4 |Atom| n² + |A| n² (5σ² + 3σ + 5)`. -/
theorem supportedWork_all_le [Fintype A] [Fintype Atom] (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (sup : Supported A S) {σ : ℕ} (small : ∀ a s, (sup.support a s).card ≤ σ) :
    (supportedWork P c sup).all ≤
      Fintype.card A * (Fintype.card S * Fintype.card S) * (1 + σ) +
        3 * (Fintype.card S * Fintype.card S) +
        4 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)) +
        Fintype.card A * (Fintype.card S * Fintype.card S) * (5 * (σ * σ) + 3 * σ + 5) := by
  have split : ∀ w : A → S → S → Work,
      (∑ a, ∑ s, ∑ t, w a s t).all = ∑ a, ∑ s, ∑ t, (w a s t).all := by
    intro w
    simp only [Work.all, Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
  have supports : (supportCheckWork P sup).all ≤
      Fintype.card A * (Fintype.card S * Fintype.card S) * (1 + σ) := by
    unfold supportCheckWork
    rw [split]
    calc ∑ a, ∑ s, ∑ x, Work.all
          (0, 0, 1, if P.trans a s x ≠ 0 then (sup.support a s).card else 0)
        ≤ ∑ _a : A, ∑ _s : S, ∑ _x : S, (1 + σ) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s _ =>
            Finset.sum_le_sum fun x _ => ?_
          simp only [Work.all]
          split_ifs
          · have := small a s
            omega
          · omega
      _ = Fintype.card A * (Fintype.card S * Fintype.card S) * (1 + σ) := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have pairs : (∑ a, ∑ s, ∑ t, supportedCoveredWork P c sup a s t).all ≤
      Fintype.card A * (Fintype.card S * Fintype.card S) * (5 * (σ * σ) + 3 * σ + 5) := by
    rw [split]
    calc ∑ a, ∑ s, ∑ t, (supportedCoveredWork P c sup a s t).all
        ≤ ∑ _a : A, ∑ _s : S, ∑ _t : S, (5 * (σ * σ) + 3 * σ + 5) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
            supportedCoveredWork_all_le P c sup a s t (small a s) (small a t)
      _ = Fintype.card A * (Fintype.card S * Fintype.card S) * (5 * (σ * σ) + 3 * σ + 5) := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have parts : (supportedWork P c sup).all = (supportCheckWork P sup).all +
      Fintype.card S * Fintype.card S + 4 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)) +
      (∑ a, ∑ s, ∑ t, supportedCoveredWork P c sup a s t).all +
      2 * (Fintype.card S * Fintype.card S) := by
    simp only [supportedWork, Work.all, Prod.fst_add, Prod.snd_add]
    ring
  rw [parts]
  omega

/-- **Four times cheaper, for every chain with small supports and enough states**: if four times the
upper bound is at most the incumbent's lower bound on products and additions, the supported check costs
at most a quarter of every accepted prefixpoint certificate's. -/
theorem supported_four_times_cheaper_of_large [Fintype A] [Fintype Atom]
    {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cert : Prefixpoint A S}
    (accepted : check P c cert = true) (sup : Supported A S) {σ : ℕ}
    (small : ∀ a s, (sup.support a s).card ≤ σ)
    (large : 4 * (Fintype.card A * (Fintype.card S * Fintype.card S) * (1 + σ) +
        3 * (Fintype.card S * Fintype.card S) +
        4 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)) +
        Fintype.card A * (Fintype.card S * Fintype.card S) * (5 * (σ * σ) + 3 * σ + 5)) ≤
      Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) *
        (Fintype.card S * Fintype.card S + 1))) +
      Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) *
        (Fintype.card S * Fintype.card S + Fintype.card S)))) :
    4 * (supportedWork P c sup).all ≤ (prefixpointWork P c cert).1 + (prefixpointWork P c cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  have upper := supportedWork_all_le P c sup small
  omega

/-- **With one action, one observation and supports of at most two states, the condition holds from
ten states on.** -/
theorem two_successors_from_ten (n : ℕ) (ten : 10 ≤ n) :
    4 * (1 * (n * n) * (1 + 2) + 3 * (n * n) + 4 * (1 * (n * n)) +
        1 * (n * n) * (5 * (2 * 2) + 3 * 2 + 5)) ≤
      1 * (n * ((n - 1) * (n * n + 1))) + 1 * (n * ((n - 1) * (n * n + n))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  rw [show k + 10 - 1 = k + 9 by omega]
  nlinarith [Nat.zero_le k, Nat.zero_le (k * k), Nat.zero_le (k * k * k), Nat.zero_le (k * k * k * k)]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
