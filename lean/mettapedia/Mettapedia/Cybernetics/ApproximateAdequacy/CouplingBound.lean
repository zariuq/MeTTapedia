import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
import Mettapedia.Cybernetics.ApproximateAdequacy.ApproxBisimulationLaws

/-!
# Coupling bounds for the behavioural pseudometric of labelled Markov chains

J. Desharnais, V. Gupta, R. Jagadeesan and P. Panangaden (*Metrics for
labelled Markov processes*, TCS 318, 2004) measure the distance of two states
of a probabilistic system by the largest difference of a real-valued modal
formula, a *functional expression*, with a discount `c` applied at each
transition.  F. van Breugel and J. Worrell characterise the same distance as
the least fixed point of the discounted Kantorovich operator.  This module
works on finite chains, over any linearly ordered field, and with the
certificates that bound that fixed point from above.

**Chains.**  A `LabelledMarkovChain` has, for each action and state, a
probability distribution of successors, and real-valued observables of
states: rewards in the metrics of N. Ferns, P. Panangaden and D. Precup
(*Metrics for finite Markov decision processes*, UAI 2004); a crisp state
label is an indicator observable.  Two chains over the same actions and
observables are compared state by state.

**Coupling bounds.**  A function `m` on pairs of states is a `CouplingBound`
at discount `c` when it is nonnegative, bounds every difference of
observables, and for every action and pair admits a coupling of the successor
distributions with `c · cost ≤ m`.  Equivalently, over `ℝ`, it is a prefixed
point of the discounted Kantorovich operator
(`Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric`); the
couplings are the coupling structures of G. Bacci, G. Bacci, K. G. Larsen and
R. Mardare (*On-the-fly exact computation of bisimilarity distances*, TACAS
2013).  A coupling bound is a finitely checkable certificate: over `ℚ` it is
decidable arithmetic.

**What it certifies** (`CouplingBound.abs_eval_sub_le`): at a pair with
`m s t ≤ ε`, every functional expression takes values within `ε` at `s` and
at `t`; a threshold reached at `s` is reached at `t` up to the margin `ε`
(`CouplingBound.threshold_transfer`).  In particular, for every open-loop
plan of `n` actions and every observable, the expected observation after
the plan differs by at most `ε / c ^ n`
(`CouplingBound.abs_expect_plan_sub_le`): discounting weakens the guarantee
on long horizons.

**Bisimulation.**  A probabilistic bisimulation relates states with equal
observables whose successor distributions have couplings supported on the
relation (the coupling form of the lifting of K. G. Larsen and A. Skou, and of
B. Jonsson and K. G. Larsen).
* Bisimilar states agree on every functional expression
  (`IsProbabilisticBisimulation.eval_eq`).
* A bisimulation gives a coupling bound vanishing on it
  (`IsProbabilisticBisimulation.couplingBound`), and the zero set of a coupling
  bound at a positive discount is a bisimulation
  (`CouplingBound.isProbabilisticBisimulation_zero`).
* A probabilistic bisimulation is an exact bisimulation of the supports
  (`IsProbabilisticBisimulation.isApproxBisimulation_support`), a
  Girard–Pappas bisimulation at precision `0`.  The converse fails: supports
  forget probabilities (the delivery example).

**Composition.**
* *Sequential*: coupling bounds compose through the infimal convolution
  `min_t (m₁ s t + m₂ t u)`, by gluing couplings (`CouplingBound.comp`); so
  closeness is transitive with additive error.
* *Parallel*: on synchronous products, coupling bounds add
  (`CouplingBound.prod`).
* *Iteration*: a coupling bound is invariant; it bounds expressions of every
  depth at once.

**Deterministic chains.**  For chains whose transitions are point masses, a
coupling bound is exactly a function with `c · m (f s) (f' t) ≤ m s t`
(`couplingBound_ofFunction_iff`).  At `c = 1` its sublevel sets are
Girard–Pappas approximate bisimulations
(`CouplingBound.isApproxBisimulation_ofFunction`), and every Girard–Pappas
approximate bisimulation gives a two-valued coupling bound
(`couplingBound_of_isApproxBisimulation`): on deterministic systems the two
notions are the same certificates.  For `c < 1` the coupling bound is weaker.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset
open Mettapedia.Cybernetics.MindWorldApproximation

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## Chains and functional expressions -/

/-- **A finite labelled Markov chain**: for each action and state a
probability distribution of successors, and real-valued observables of
states. -/
structure LabelledMarkovChain (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] (A Atom S : Type*)
    [Fintype S] where
  /-- The successor distribution of `s` under action `a`. -/
  trans : A → S → S → 𝕜
  isDistribution : ∀ a s, IsDistribution (trans a s)
  /-- The value of observable `i` at a state. -/
  observe : Atom → S → 𝕜

/-- **Functional expressions** (Desharnais, Gupta, Jagadeesan, Panangaden):
real-valued modal formulas.  `next a φ` is the discounted expectation of `φ`
after action `a`, and `sub φ q` is truncated subtraction `max (φ - q) 0`. -/
inductive FunctionalExpression (𝕜 A Atom : Type*) : Type _
  | one
  | observe (i : Atom)
  | oneMinus (φ : FunctionalExpression 𝕜 A Atom)
  | min (φ ψ : FunctionalExpression 𝕜 A Atom)
  | max (φ ψ : FunctionalExpression 𝕜 A Atom)
  | sub (φ : FunctionalExpression 𝕜 A Atom) (q : 𝕜)
  | next (a : A) (φ : FunctionalExpression 𝕜 A Atom)

namespace FunctionalExpression

variable {A Atom S : Type*} [Fintype S]

/-- The value of an expression at a state, at discount `c`. -/
def eval (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜) : FunctionalExpression 𝕜 A Atom → S → 𝕜
  | one, _ => 1
  | observe i, s => P.observe i s
  | oneMinus φ, s => 1 - φ.eval P c s
  | min φ ψ, s => Min.min (φ.eval P c s) (ψ.eval P c s)
  | max φ ψ, s => Max.max (φ.eval P c s) (ψ.eval P c s)
  | sub φ q, s => Max.max (φ.eval P c s - q) 0
  | next a φ, s => c * expect (P.trans a s) (φ.eval P c)

/-- The modal depth: the number of nested transitions. -/
def depth : FunctionalExpression 𝕜 A Atom → ℕ
  | one => 0
  | observe _ => 0
  | oneMinus φ => φ.depth
  | min φ ψ => Max.max φ.depth ψ.depth
  | max φ ψ => Max.max φ.depth ψ.depth
  | sub φ _ => φ.depth
  | next _ φ => φ.depth + 1

/-- The expression `φ` evaluated after an open-loop plan of actions. -/
def afterPlan : List A → FunctionalExpression 𝕜 A Atom → FunctionalExpression 𝕜 A Atom
  | [], φ => φ
  | a :: plan, φ => next a (afterPlan plan φ)

end FunctionalExpression

open FunctionalExpression

variable {A Atom S T U : Type*} [Fintype S] [Fintype T] [Fintype U]

/-! ## Coupling bounds and soundness -/

/-- **A coupling bound** for the chains `P` and `Q` at discount `c`: a
nonnegative function on pairs of states that bounds every difference of
observables and, for every action and pair, the discounted cost of some
coupling of the successor distributions. -/
structure CouplingBound (P : LabelledMarkovChain 𝕜 A Atom S) (Q : LabelledMarkovChain 𝕜 A Atom T)
    (c : 𝕜) (m : S → T → 𝕜) : Prop where
  nonneg : ∀ s t, 0 ≤ m s t
  observe_le : ∀ i s t, |P.observe i s - Q.observe i t| ≤ m s t
  step_le : ∀ a s t, ∃ ω : Coupling (P.trans a s) (Q.trans a t), c * ω.cost m ≤ m s t

variable {P : LabelledMarkovChain 𝕜 A Atom S} {Q : LabelledMarkovChain 𝕜 A Atom T}
  {R : LabelledMarkovChain 𝕜 A Atom U} {c : 𝕜} {m : S → T → 𝕜}

/-- **Soundness: a coupling bound bounds every functional expression.** -/
theorem CouplingBound.abs_eval_sub_le (bound : CouplingBound P Q c m) (c_nonneg : 0 ≤ c) :
    ∀ (φ : FunctionalExpression 𝕜 A Atom) (s : S) (t : T),
      |φ.eval P c s - φ.eval Q c t| ≤ m s t
  | .one, s, t => by
      simp only [eval, sub_self, abs_zero]
      exact bound.nonneg s t
  | .observe i, s, t => bound.observe_le i s t
  | .oneMinus φ, s, t => by
      simp only [eval]
      rw [show 1 - φ.eval P c s - (1 - φ.eval Q c t) = -(φ.eval P c s - φ.eval Q c t) by ring,
        abs_neg]
      exact bound.abs_eval_sub_le c_nonneg φ s t
  | .min φ ψ, s, t => (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le (bound.abs_eval_sub_le c_nonneg φ s t) (bound.abs_eval_sub_le c_nonneg ψ s t))
  | .max φ ψ, s, t => (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (bound.abs_eval_sub_le c_nonneg φ s t) (bound.abs_eval_sub_le c_nonneg ψ s t))
  | .sub φ q, s, t => by
      simp only [eval]
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
      · rw [sub_sub_sub_cancel_right]
        exact bound.abs_eval_sub_le c_nonneg φ s t
      · rw [sub_self, abs_zero]
        exact bound.nonneg s t
  | .next a φ, s, t => by
      obtain ⟨ω, le⟩ := bound.step_le a s t
      have coupled := ω.abs_expect_sub_le fun x y => bound.abs_eval_sub_le c_nonneg φ x y
      simp only [eval]
      rw [← mul_sub, abs_mul, abs_of_nonneg c_nonneg]
      exact (mul_le_mul_of_nonneg_left coupled c_nonneg).trans le

/-- **States within `ε` agree within `ε` on every functional expression.** -/
theorem CouplingBound.abs_eval_sub_le_of_le (bound : CouplingBound P Q c m) (c_nonneg : 0 ≤ c)
    {s : S} {t : T} {ε : 𝕜} (close : m s t ≤ ε) (φ : FunctionalExpression 𝕜 A Atom) :
    |φ.eval P c s - φ.eval Q c t| ≤ ε :=
  (bound.abs_eval_sub_le c_nonneg φ s t).trans close

/-- **Thresholds transfer with a margin**: if an expression reaches `q` at `s`,
it reaches `q - m s t` at `t`. -/
theorem CouplingBound.threshold_transfer (bound : CouplingBound P Q c m) (c_nonneg : 0 ≤ c)
    (φ : FunctionalExpression 𝕜 A Atom) {s : S} {t : T} {q : 𝕜} (reaches : q ≤ φ.eval P c s) :
    q - m s t ≤ φ.eval Q c t := by
  have := (abs_le.mp (bound.abs_eval_sub_le c_nonneg φ s t)).2
  linarith

theorem CouplingBound.mono_discount (bound : CouplingBound P Q c m) {c' : 𝕜}
    (le : c' ≤ c) : CouplingBound P Q c' m where
  nonneg := bound.nonneg
  observe_le := bound.observe_le
  step_le a s t := by
    obtain ⟨ω, bounded⟩ := bound.step_le a s t
    exact ⟨ω, (mul_le_mul_of_nonneg_right le (ω.cost_nonneg bound.nonneg)).trans bounded⟩

/-! ### Plans: predicting observations over time -/

section Plans

variable [DecidableEq S]

/-- The distribution of states after an open-loop plan of actions. -/
def LabelledMarkovChain.planDistribution (P : LabelledMarkovChain 𝕜 A Atom S) :
    List A → S → S → 𝕜
  | [], s => dirac s
  | a :: plan, s => fun x => ∑ y, P.trans a s y * P.planDistribution plan y x

omit [IsStrictOrderedRing 𝕜] in
/-- **An expression after a plan is the discounted expectation under the plan's
distribution.** -/
theorem eval_afterPlan (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜)
    (φ : FunctionalExpression 𝕜 A Atom) :
    ∀ (plan : List A) (s : S), (afterPlan plan φ).eval P c s =
      c ^ plan.length * expect (P.planDistribution plan s) (φ.eval P c)
  | [], s => by
      simp only [afterPlan, List.length_nil, pow_zero, one_mul,
        LabelledMarkovChain.planDistribution]
      exact (expect_dirac s _).symm
  | a :: plan, s => by
      change c * expect (P.trans a s) ((afterPlan plan φ).eval P c) =
        c ^ (plan.length + 1) *
          expect (fun x => ∑ y, P.trans a s y * P.planDistribution plan y x) (φ.eval P c)
      unfold expect
      simp_rw [eval_afterPlan P c φ plan, expect]
      calc c * ∑ y, P.trans a s y *
            (c ^ plan.length * ∑ x, P.planDistribution plan y x * φ.eval P c x)
          = ∑ y, ∑ x, c ^ (plan.length + 1) *
              (P.trans a s y * P.planDistribution plan y x * φ.eval P c x) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
        _ = ∑ x, ∑ y, c ^ (plan.length + 1) *
              (P.trans a s y * P.planDistribution plan y x * φ.eval P c x) := Finset.sum_comm
        _ = c ^ (plan.length + 1) *
              ∑ x, (∑ y, P.trans a s y * P.planDistribution plan y x) * φ.eval P c x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]

end Plans

/-- **Predictions along a plan**: at a pair with coupling bound at most `ε`,
for every open-loop plan and every expression, the expectations after the plan
differ by at most `ε / c ^ n`, where `n` is the length of the plan. -/
theorem CouplingBound.abs_expect_plan_sub_le [DecidableEq S] [DecidableEq T]
    (bound : CouplingBound P Q c m) (c_pos : 0 < c) (plan : List A)
    (φ : FunctionalExpression 𝕜 A Atom) (s : S) (t : T) :
    |expect (P.planDistribution plan s) (φ.eval P c) -
        expect (Q.planDistribution plan t) (φ.eval Q c)| ≤ m s t / c ^ plan.length := by
  have sound := bound.abs_eval_sub_le c_pos.le (afterPlan plan φ) s t
  rw [eval_afterPlan, eval_afterPlan, ← mul_sub, abs_mul,
    abs_of_pos (pow_pos c_pos _)] at sound
  rw [le_div_iff₀ (pow_pos c_pos _), mul_comm]
  exact sound

/-! ## Probabilistic bisimulation -/

/-- **A probabilistic bisimulation** between two chains: related states have
equal observables, and for every action their successor distributions have a
coupling supported on the relation. -/
def IsProbabilisticBisimulation (P : LabelledMarkovChain 𝕜 A Atom S)
    (Q : LabelledMarkovChain 𝕜 A Atom T) (R : S → T → Prop) : Prop :=
  ∀ ⦃s t⦄, R s t → (∀ i, P.observe i s = Q.observe i t) ∧
    ∀ a, ∃ ω : Coupling (P.trans a s) (Q.trans a t), ∀ x y, ω.weight x y ≠ 0 → R x y

/-- Two states are probabilistically bisimilar. -/
def ProbabilisticallyBisimilar (P : LabelledMarkovChain 𝕜 A Atom S)
    (Q : LabelledMarkovChain 𝕜 A Atom T) (s : S) (t : T) : Prop :=
  ∃ R, IsProbabilisticBisimulation P Q R ∧ R s t

omit [IsStrictOrderedRing 𝕜] in
/-- **Bisimilar states agree on every functional expression**, at every
discount. -/
theorem IsProbabilisticBisimulation.eval_eq {Rel : S → T → Prop}
    (bisimulation : IsProbabilisticBisimulation P Q Rel) (c : 𝕜) :
    ∀ (φ : FunctionalExpression 𝕜 A Atom) {s : S} {t : T}, Rel s t → φ.eval P c s = φ.eval Q c t
  | .one, _, _, _ => rfl
  | .observe i, _, _, related => (bisimulation related).1 i
  | .oneMinus φ, _, _, related => by
      simp only [eval]
      rw [bisimulation.eval_eq c φ related]
  | .min φ ψ, _, _, related => by
      simp only [eval]
      rw [bisimulation.eval_eq c φ related, bisimulation.eval_eq c ψ related]
  | .max φ ψ, _, _, related => by
      simp only [eval]
      rw [bisimulation.eval_eq c φ related, bisimulation.eval_eq c ψ related]
  | .sub φ q, _, _, related => by
      simp only [eval]
      rw [bisimulation.eval_eq c φ related]
  | .next a φ, s, t, related => by
      obtain ⟨ω, supported⟩ := (bisimulation related).2 a
      simp only [eval]
      rw [← sub_eq_zero, ← mul_sub, ω.expect_sub_expect]
      have terms : ∀ x y, ω.weight x y * (φ.eval P c x - φ.eval Q c y) = 0 := by
        intro x y
        by_cases zero : ω.weight x y = 0
        · rw [zero, zero_mul]
        · rw [bisimulation.eval_eq c φ (supported x y zero), sub_self, mul_zero]
      simp [terms]

omit [IsStrictOrderedRing 𝕜] in
theorem ProbabilisticallyBisimilar.eval_eq {s : S} {t : T}
    (bisimilar : ProbabilisticallyBisimilar P Q s t) (c : 𝕜) (φ : FunctionalExpression 𝕜 A Atom) :
    φ.eval P c s = φ.eval Q c t :=
  let ⟨_, bisimulation, related⟩ := bisimilar
  bisimulation.eval_eq c φ related

/-- **The zero set of a coupling bound at a positive discount is a
probabilistic bisimulation.** -/
theorem CouplingBound.isProbabilisticBisimulation_zero (bound : CouplingBound P Q c m)
    (c_pos : 0 < c) : IsProbabilisticBisimulation P Q fun s t => m s t = 0 := by
  intro s t zero
  refine ⟨fun i => ?_, fun a => ?_⟩
  · have := bound.observe_le i s t
    rw [zero] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  · obtain ⟨ω, le⟩ := bound.step_le a s t
    refine ⟨ω, fun x y positive => ω.eq_zero_of_cost_nonpos bound.nonneg ?_ positive⟩
    rw [zero] at le
    exact (mul_nonpos_iff_pos_imp_nonpos.mp le).1 c_pos

/-- **A probabilistic bisimulation gives a coupling bound vanishing on it**,
with the value `B` elsewhere, for any `B` bounding the differences of
observables, at every discount `c ≤ 1`. -/
theorem IsProbabilisticBisimulation.couplingBound {Rel : S → T → Prop}
    [∀ s t, Decidable (Rel s t)] (bisimulation : IsProbabilisticBisimulation P Q Rel)
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) {B : 𝕜} (B_nonneg : 0 ≤ B)
    (observe_le : ∀ i s t, |P.observe i s - Q.observe i t| ≤ B) :
    CouplingBound P Q c fun s t => if Rel s t then 0 else B where
  nonneg s t := by split_ifs <;> first | exact le_rfl | exact B_nonneg
  observe_le i s t := by
    split_ifs with related
    · rw [(bisimulation related).1 i, sub_self, abs_zero]
    · exact observe_le i s t
  step_le a s t := by
    by_cases related : Rel s t
    · obtain ⟨ω, supported⟩ := (bisimulation related).2 a
      refine ⟨ω, ?_⟩
      have zero : ω.cost (fun s t => if Rel s t then 0 else B) = 0 := by
        unfold Coupling.cost
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        by_cases positive : ω.weight x y = 0
        · rw [positive, zero_mul]
        · simp only [if_pos (supported x y positive), mul_zero]
      rw [zero, mul_zero, if_pos related]
    · refine ⟨Coupling.independent (P.isDistribution a s) (Q.isDistribution a t), ?_⟩
      rw [if_neg related]
      have cost_le := (Coupling.independent (P.isDistribution a s)
        (Q.isDistribution a t)).cost_le_of_le (P.isDistribution a s)
          (m := fun s t => if Rel s t then 0 else B) (B := B)
          fun x y => by split_ifs <;> first | exact B_nonneg | exact le_rfl
      calc c * _ ≤ c * B := mul_le_mul_of_nonneg_left cost_le c_nonneg
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right c_le B_nonneg
        _ = B := one_mul B

/-! ### Supports: probabilistic bisimulation forgets to exact bisimulation -/

section Supports

variable [Fintype Atom]

/-- The largest difference of an observable between two observation
vectors. -/
def observationGap (o o' : Atom → 𝕜) : 𝕜 :=
  Finset.univ.fold Max.max 0 fun i => |o i - o' i|

omit [IsStrictOrderedRing 𝕜] in
theorem observationGap_le_iff {o o' : Atom → 𝕜} {ε : 𝕜} :
    observationGap o o' ≤ ε ↔ 0 ≤ ε ∧ ∀ i, |o i - o' i| ≤ ε := by
  rw [observationGap, Finset.fold_max_le]
  exact and_congr Iff.rfl ⟨fun all i => all i (Finset.mem_univ i), fun all i _ => all i⟩

theorem observationGap_self (o : Atom → 𝕜) : observationGap o o = 0 :=
  le_antisymm (observationGap_le_iff.mpr ⟨le_rfl, fun i => by rw [sub_self, abs_zero]⟩)
    (by rw [observationGap, Finset.le_fold_max]; exact Or.inl le_rfl)

theorem observationGap_triangle (o o' o'' : Atom → 𝕜) :
    observationGap o o'' ≤ observationGap o o' + observationGap o' o'' := by
  have first := (observationGap_le_iff (o := o) (o' := o')).mp le_rfl
  have second := (observationGap_le_iff (o := o') (o' := o'')).mp le_rfl
  exact observationGap_le_iff.mpr ⟨add_nonneg first.1 second.1, fun i =>
    (abs_sub_le _ _ _).trans (add_le_add (first.2 i) (second.2 i))⟩

omit [IsStrictOrderedRing 𝕜] in
theorem observationGap_comm (o o' : Atom → 𝕜) : observationGap o o' = observationGap o' o := by
  unfold observationGap
  congr 1
  funext i
  exact abs_sub_comm _ _

/-- The vector of observables of a state. -/
def LabelledMarkovChain.observation (P : LabelledMarkovChain 𝕜 A Atom S) (s : S) : Atom → 𝕜 :=
  fun i => P.observe i s

/-- The support of a transition: the successors of positive probability. -/
def LabelledMarkovChain.supportStep (P : LabelledMarkovChain 𝕜 A Atom S) (a : A) (s x : S) :
    Prop :=
  P.trans a s x ≠ 0

/-- **A probabilistic bisimulation is an exact bisimulation of the supports**:
a Girard–Pappas approximate bisimulation at precision `0` for every
action. -/
theorem IsProbabilisticBisimulation.isApproxBisimulation_support {Rel : S → T → Prop}
    (bisimulation : IsProbabilisticBisimulation P Q Rel) (a : A) :
    IsApproxBisimulation observationGap (P.supportStep a) (Q.supportStep a) P.observation
      Q.observation 0 Rel := by
  have same : ∀ {s t}, Rel s t → P.observation s = Q.observation t := fun related =>
    funext fun i => (bisimulation related).1 i
  refine ⟨⟨fun s t related => ?_, fun s t related x moved => ?_⟩,
    ⟨fun t s related => ?_, fun t s related y moved => ?_⟩⟩
  · rw [same related, observationGap_self]
  · obtain ⟨ω, supported⟩ := (bisimulation related).2 a
    have row : ∑ y, ω.weight x y ≠ 0 := by rw [ω.sum_right x]; exact moved
    obtain ⟨y, _, positive⟩ := Finset.exists_ne_zero_of_sum_ne_zero row
    refine ⟨y, fun zero => positive ?_, supported x y positive⟩
    exact ω.weight_eq_zero_of_right zero x
  · change Rel s t at related
    rw [same related, observationGap_self]
  · change Rel s t at related
    obtain ⟨ω, supported⟩ := (bisimulation related).2 a
    have column : ∑ x, ω.weight x y ≠ 0 := by rw [ω.sum_left y]; exact moved
    obtain ⟨x, _, positive⟩ := Finset.exists_ne_zero_of_sum_ne_zero column
    refine ⟨x, fun zero => positive ?_, supported x y positive⟩
    exact ω.weight_eq_zero_of_left zero y

end Supports

/-! ## Sequential composition: the infimal convolution -/

section Sequential

variable [Nonempty T]

/-- The infimal convolution of two bounds through the middle chain. -/
def infConvolution (m₁ : S → T → 𝕜) (m₂ : T → U → 𝕜) (s : S) (u : U) : 𝕜 :=
  Finset.univ.inf' Finset.univ_nonempty fun t => m₁ s t + m₂ t u

omit [IsStrictOrderedRing 𝕜] [Fintype S] [Fintype U] in
theorem infConvolution_le (m₁ : S → T → 𝕜) (m₂ : T → U → 𝕜) (s : S) (t : T) (u : U) :
    infConvolution m₁ m₂ s u ≤ m₁ s t + m₂ t u :=
  Finset.inf'_le _ (Finset.mem_univ t)

/-- **Coupling bounds compose sequentially**: the infimal convolution of a bound
for `P, Q` and a bound for `Q, R` is a bound for `P, R`.  Closeness is
transitive, with additive error. -/
theorem CouplingBound.comp {m₁ : S → T → 𝕜} {m₂ : T → U → 𝕜} (first : CouplingBound P Q c m₁)
    (second : CouplingBound Q R c m₂) (c_nonneg : 0 ≤ c) :
    CouplingBound P R c (infConvolution m₁ m₂) where
  nonneg s u := Finset.le_inf' _ _ fun t _ => add_nonneg (first.nonneg s t) (second.nonneg t u)
  observe_le i s u := Finset.le_inf' _ _ fun t _ =>
    (abs_sub_le _ (Q.observe i t) _).trans (add_le_add (first.observe_le i s t)
      (second.observe_le i t u))
  step_le a s u := by
    obtain ⟨t, _, attained⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := T))
      fun t => m₁ s t + m₂ t u
    obtain ⟨ω₁, le₁⟩ := first.step_le a s t
    obtain ⟨ω₂, le₂⟩ := second.step_le a t u
    refine ⟨ω₁.glue ω₂, ?_⟩
    have glued := ω₁.cost_glue_le ω₂ (m₃ := infConvolution m₁ m₂)
      fun x y z => infConvolution_le m₁ m₂ x y z
    have attained' : infConvolution m₁ m₂ s u = m₁ s t + m₂ t u := attained
    rw [attained']
    calc c * (ω₁.glue ω₂).cost _ ≤ c * (ω₁.cost m₁ + ω₂.cost m₂) :=
          mul_le_mul_of_nonneg_left glued c_nonneg
      _ = c * ω₁.cost m₁ + c * ω₂.cost m₂ := mul_add _ _ _
      _ ≤ m₁ s t + m₂ t u := add_le_add le₁ le₂

/-- **Predictions compose through a middle chain**, with additive error. -/
theorem CouplingBound.abs_eval_sub_le_comp {m₁ : S → T → 𝕜} {m₂ : T → U → 𝕜}
    (first : CouplingBound P Q c m₁) (second : CouplingBound Q R c m₂) (c_nonneg : 0 ≤ c)
    (φ : FunctionalExpression 𝕜 A Atom) (s : S) (t : T) (u : U) :
    |φ.eval P c s - φ.eval R c u| ≤ m₁ s t + m₂ t u :=
  ((first.comp second c_nonneg).abs_eval_sub_le c_nonneg φ s u).trans
    (infConvolution_le m₁ m₂ s t u)

end Sequential

/-! ## Parallel composition: synchronous products -/

section Parallel

variable {Atom₁ Atom₂ S₁ S₂ T₁ T₂ : Type*} [Fintype S₁] [Fintype S₂] [Fintype T₁] [Fintype T₂]

/-- **The synchronous product of two chains**: both components move under the
same action, independently; the observables are those of either component. -/
def LabelledMarkovChain.prod (P : LabelledMarkovChain 𝕜 A Atom₁ S₁)
    (Q : LabelledMarkovChain 𝕜 A Atom₂ S₂) : LabelledMarkovChain 𝕜 A (Atom₁ ⊕ Atom₂) (S₁ × S₂) where
  trans a p := prodWeight (P.trans a p.1) (Q.trans a p.2)
  isDistribution a p := (P.isDistribution a p.1).prod (Q.isDistribution a p.2)
  observe i p := Sum.elim (fun i => P.observe i p.1) (fun j => Q.observe j p.2) i

/-- **Coupling bounds add under synchronous products.** -/
theorem CouplingBound.prod {P : LabelledMarkovChain 𝕜 A Atom₁ S₁}
    {P' : LabelledMarkovChain 𝕜 A Atom₁ T₁} {Q : LabelledMarkovChain 𝕜 A Atom₂ S₂}
    {Q' : LabelledMarkovChain 𝕜 A Atom₂ T₂} {m₁ : S₁ → T₁ → 𝕜} {m₂ : S₂ → T₂ → 𝕜}
    (first : CouplingBound P P' c m₁) (second : CouplingBound Q Q' c m₂) :
    CouplingBound (P.prod Q) (P'.prod Q') c fun p q => m₁ p.1 q.1 + m₂ p.2 q.2 where
  nonneg p q := add_nonneg (first.nonneg p.1 q.1) (second.nonneg p.2 q.2)
  observe_le i p q := by
    cases i with
    | inl i =>
        exact (first.observe_le i p.1 q.1).trans (le_add_of_nonneg_right (second.nonneg p.2 q.2))
    | inr j =>
        exact (second.observe_le j p.2 q.2).trans (le_add_of_nonneg_left (first.nonneg p.1 q.1))
  step_le a p q := by
    obtain ⟨ω₁, le₁⟩ := first.step_le a p.1 q.1
    obtain ⟨ω₂, le₂⟩ := second.step_le a p.2 q.2
    refine ⟨ω₁.prod ω₂, ?_⟩
    have split := Coupling.cost_prod_add ω₁ ω₂ (P.isDistribution a p.1) (Q.isDistribution a p.2)
      m₁ m₂
    have bounded : c * (ω₁.prod ω₂).cost (fun p q => m₁ p.1 q.1 + m₂ p.2 q.2) ≤
        m₁ p.1 q.1 + m₂ p.2 q.2 := by
      rw [split, mul_add]
      exact add_le_add le₁ le₂
    exact bounded

end Parallel

/-! ## Deterministic chains -/

section Deterministic

variable [DecidableEq S] [DecidableEq T]

/-- The chain of a deterministic system: point-mass transitions. -/
def LabelledMarkovChain.ofFunction (next : A → S → S) (observe : Atom → S → 𝕜) :
    LabelledMarkovChain 𝕜 A Atom S where
  trans a s := dirac (next a s)
  isDistribution a s := isDistribution_dirac (next a s)
  observe := observe

variable {f : A → S → S} {f' : A → T → T} {obs : Atom → S → 𝕜} {obs' : Atom → T → 𝕜}

/-- **On deterministic chains a coupling bound is a function with
`c · m (f s) (f' t) ≤ m s t`.** -/
theorem couplingBound_ofFunction_iff :
    CouplingBound (LabelledMarkovChain.ofFunction f obs) (LabelledMarkovChain.ofFunction f' obs')
        c m ↔
      (∀ s t, 0 ≤ m s t) ∧ (∀ i s t, |obs i s - obs' i t| ≤ m s t) ∧
        ∀ a s t, c * m (f a s) (f' a t) ≤ m s t := by
  constructor
  · intro bound
    refine ⟨bound.nonneg, bound.observe_le, fun a s t => ?_⟩
    obtain ⟨ω, le⟩ := bound.step_le a s t
    rwa [ω.cost_of_eq_dirac rfl rfl] at le
  · rintro ⟨nonneg, observe_le, step⟩
    refine ⟨nonneg, observe_le, fun a s t => ⟨Coupling.ofDirac (f a s) (f' a t), ?_⟩⟩
    have key : c * (Coupling.ofDirac (𝕜 := 𝕜) (f a s) (f' a t)).cost m ≤ m s t := by
      rw [Coupling.cost_dirac]
      exact step a s t
    exact key

variable [Fintype Atom]

/-- **At discount `1`, the sublevel sets of a coupling bound on deterministic
chains are Girard–Pappas approximate bisimulations**, for every action. -/
theorem CouplingBound.isApproxBisimulation_ofFunction
    (bound : CouplingBound (LabelledMarkovChain.ofFunction f obs)
      (LabelledMarkovChain.ofFunction f' obs') 1 m) (a : A) (ε : 𝕜) :
    IsApproxBisimulation observationGap (fun s s' => f a s = s') (fun t t' => f' a t = t')
      (fun s i => obs i s) (fun t i => obs' i t) ε fun s t => m s t ≤ ε := by
  obtain ⟨nonneg, observe_le, step⟩ := couplingBound_ofFunction_iff.mp bound
  refine ⟨⟨fun s t close => ?_, fun s t close s' moved => ?_⟩,
    ⟨fun t s close => ?_, fun t s close t' moved => ?_⟩⟩
  · exact observationGap_le_iff.mpr ⟨(nonneg s t).trans close,
      fun i => (observe_le i s t).trans close⟩
  · subst moved
    exact ⟨f' a t, rfl, ((one_mul _).symm.le.trans (step a s t)).trans close⟩
  · change m s t ≤ ε at close
    exact observationGap_le_iff.mpr ⟨(nonneg s t).trans close,
      fun i => by rw [abs_sub_comm]; exact (observe_le i s t).trans close⟩
  · change m s t ≤ ε at close
    subst moved
    exact ⟨f a s, rfl, ((one_mul _).symm.le.trans (step a s t)).trans close⟩

/-- **Every Girard–Pappas approximate bisimulation of deterministic systems gives
a two-valued coupling bound**, at every discount `c ≤ 1`. -/
theorem couplingBound_of_isApproxBisimulation [Nonempty A] {Rel : S → T → Prop}
    [∀ s t, Decidable (Rel s t)] {ε B : 𝕜}
    (bisimulation : ∀ a, IsApproxBisimulation observationGap (fun s s' => f a s = s')
      (fun t t' => f' a t = t') (fun s i => obs i s) (fun t i => obs' i t) ε Rel)
    (ε_nonneg : 0 ≤ ε) (le : ε ≤ B) (observe_le : ∀ i s t, |obs i s - obs' i t| ≤ B)
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    CouplingBound (LabelledMarkovChain.ofFunction f obs) (LabelledMarkovChain.ofFunction f' obs')
      c fun s t => if Rel s t then ε else B := by
  have B_nonneg : 0 ≤ B := ε_nonneg.trans le
  have below : ∀ s t, (if Rel s t then ε else B) ≤ B := fun s t => by
    split_ifs
    · exact le
    · exact le_rfl
  refine couplingBound_ofFunction_iff.mpr ⟨fun s t => ?_, fun i s t => ?_, fun a s t => ?_⟩
  · split_ifs
    · exact ε_nonneg
    · exact B_nonneg
  · split_ifs with related
    · exact (inferInstance : Nonempty A).elim fun a₀ =>
        (observationGap_le_iff.mp ((bisimulation a₀).1.close related)).2 i
    · exact observe_le i s t
  · by_cases related : Rel s t
    · obtain ⟨_, moved, related'⟩ := (bisimulation a).1.forth related (f a s) rfl
      subst moved
      rw [if_pos related, if_pos related']
      calc c * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right c_le ε_nonneg
        _ = ε := one_mul ε
    · rw [if_neg related]
      calc c * _ ≤ c * B := mul_le_mul_of_nonneg_left (below _ _) c_nonneg
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right c_le B_nonneg
        _ = B := one_mul B

end Deterministic

end Mettapedia.Cybernetics.ApproximateAdequacy
