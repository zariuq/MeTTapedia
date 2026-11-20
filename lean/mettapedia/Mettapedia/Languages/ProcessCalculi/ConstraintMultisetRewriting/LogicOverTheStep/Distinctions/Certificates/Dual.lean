import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Verdicts

/-!
# The dual post-fixpoint: a lower certificate for a discount below one

A function `m` on pairs with `m ≤` its own Kantorovich step is a *post-fixpoint*.

**The lemma** (`le_bisimulationMetric_of_le_step`): at a discount `0 ≤ c < 1`, every post-fixpoint
lies below the bisimulation metric. Proof: let `M` be the largest excess `m - metric` over the
finitely many pairs. The metric is a fixed point, and the lifting moves by at most a uniform
perturbation of the cost, so the step of `m` is at most `metric + c · M`; hence `M ≤ c · M`, and
`M ≤ 0` because `c < 1`.

**It fails at `c = 1`**: there the operator has fixed points above the least one. On two
self-loops with the same observation the metric is zero, while the kernel one off the diagonal is a
post-fixpoint; the controls exhibit both as accepted certificates.

**The certificate** (`DualPostfixpoint`): a rational kernel and, for some pairs, an action with two
potentials `f, g` whose differences `f u - g v` the kernel bounds. The checker (`dualCheck`) accepts
when at every pair the kernel is at most zero, or at most some observation difference, or at most
`c` times the difference of the expected potentials. Only weak duality is used: under any
coupling the difference of expected potentials is at most the expected kernel, so the potentials
bound the Kantorovich lifting from below.

* `dualCheck_le_step`: acceptance makes the kernel a post-fixpoint on the real chain, at every
  discount `0 ≤ c`;
* `dualCheck_sound`: acceptance implies kernel `≤` metric pointwise, at `0 ≤ c < 1`;
* with an accepted prefixpoint the two bracket the metric (`measureByDual`): exact when they meet
  (`bisimulationMetric_eq_of_dual_meet`, `measureByDual_exact`), otherwise an interval
  (`measureByDual_between`), with the verdicts of `Verdicts`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S T : Type*} [Fintype S] [Fintype T]

/-! ## The lemma -/

section Lemma

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℝ A Atom S}
  {Q : LabelledMarkovChain ℝ A Atom T} {c : ℝ}

/-- **Post-fixpoints lie below the metric when the discount is below one.** -/
theorem le_bisimulationMetric_of_le_step (c_nonneg : 0 ≤ c) (c_lt : c < 1) {m : S → T → ℝ}
    (post : ∀ s t, m s t ≤ kantorovichStep P Q c m s t) (s : S) (t : T) :
    m s t ≤ bisimulationMetric P Q c s t := by
  classical
  have nonempty : (Finset.univ : Finset (S × T)).Nonempty := ⟨(s, t), Finset.mem_univ _⟩
  set M := Finset.univ.sup' nonempty fun p : S × T =>
    m p.1 p.2 - bisimulationMetric P Q c p.1 p.2 with M_def
  have excess_le : ∀ x y, m x y - bisimulationMetric P Q c x y ≤ M := fun x y =>
    Finset.le_sup' (fun p : S × T => m p.1 p.2 - bisimulationMetric P Q c p.1 p.2)
      (Finset.mem_univ (x, y))
  suffices M_nonpos : M ≤ 0 by linarith [excess_le s t]
  by_contra not_nonpos
  have positive : 0 < M := not_le.mp not_nonpos
  have step_le : ∀ x y, kantorovichStep P Q c m x y ≤ bisimulationMetric P Q c x y + c * M := by
    intro x y
    have cM : 0 ≤ c * M := mul_nonneg c_nonneg positive.le
    refine kantorovichStep_le_iff.mpr ⟨?_, fun a => ?_⟩
    · have base := approxMetric_le_bisimulationMetric (P := P) (Q := Q) c_nonneg c_lt.le 0 x y
      change observationDistance P Q x y ≤ bisimulationMetric P Q c x y at base
      linarith
    · have lifted := kantorovich_le_add (P.isDistribution a x) (Q.isDistribution a y) (m := m)
        (m' := bisimulationMetric P Q c) (η := M) fun u v => by linarith [excess_le u v]
      have fixed := mul_kantorovich_bisimulationMetric_le (P := P) (Q := Q) c_nonneg c_lt.le a x y
      calc c * kantorovich m (P.trans a x) (Q.trans a y)
          ≤ c * (kantorovich (bisimulationMetric P Q c) (P.trans a x) (Q.trans a y) + M) :=
            mul_le_mul_of_nonneg_left lifted c_nonneg
        _ = c * kantorovich (bisimulationMetric P Q c) (P.trans a x) (Q.trans a y) + c * M :=
            mul_add _ _ _
        _ ≤ bisimulationMetric P Q c x y + c * M := by linarith
  obtain ⟨p, _, attained⟩ := Finset.exists_mem_eq_sup' nonempty fun p : S × T =>
    m p.1 p.2 - bisimulationMetric P Q c p.1 p.2
  have at_p := (post p.1 p.2).trans (step_le p.1 p.2)
  have value : M = m p.1 p.2 - bisimulationMetric P Q c p.1 p.2 := M_def.trans attained
  have shrink : M ≤ c * M := by linarith
  nlinarith [mul_pos (sub_pos.mpr c_lt) positive]

end Lemma

/-! ## The certificate and its checker -/

/-- **A dual post-fixpoint certificate** for a chain with actions `A` on states `S`: a rational
kernel claimed to lie below the metric and, for some pairs, an action with two potentials. -/
structure DualPostfixpoint (A S : Type*) where
  /-- The kernel claimed to lie below the metric. -/
  kernel : S → S → ℚ
  /-- The listed actions and potentials. -/
  witness : S → S → Option (A × (S → ℚ) × (S → ℚ))

section Checker

variable (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (dual : DualPostfixpoint A S)

/-- **One pair.** The kernel there is at most zero, or at most some observation difference, or the
listed action and potentials `f, g`, whose differences `f u - g v` the kernel bounds everywhere,
have discounted expected difference at least the kernel at the pair. -/
def dualAt [Fintype Atom] (s t : S) : Bool :=
  decide (dual.kernel s t ≤ 0) ||
    decide (∃ i, dual.kernel s t ≤ |P.observe i s - P.observe i t|) ||
    match dual.witness s t with
    | some (a, f, g) =>
        decide (∀ u v, f u - g v ≤ dual.kernel u v) &&
          decide (dual.kernel s t ≤ c * (expect (P.trans a s) f - expect (P.trans a t) g))
    | none => false

/-- **The checker** of dual post-fixpoint certificates. -/
def dualCheck [Fintype Atom] : Bool :=
  decide (∀ s t, dualAt P c dual s t = true)

end Checker

section Soundness

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ}
  {dual : DualPostfixpoint A S}

omit [Fintype A] [Fintype Atom] in
theorem expect_realChain (P : LabelledMarkovChain ℚ A Atom S) (a : A) (s : S) (f : S → ℚ) :
    expect ((realChain P).trans a s) (fun u => (f u : ℝ)) = ((expect (P.trans a s) f : ℚ) : ℝ) := by
  simp [expect]

/-- **Acceptance makes the kernel a post-fixpoint** on the real chain, at every discount `0 ≤ c`. -/
theorem dualCheck_le_step (accepted : dualCheck P c dual = true) (c_nonneg : 0 ≤ c) (s t : S) :
    (dual.kernel s t : ℝ) ≤
      kantorovichStep (realChain P) (realChain P) (c : ℝ) (fun u v => (dual.kernel u v : ℝ)) s t := by
  have here := of_decide_eq_true accepted s t
  simp only [dualAt, Bool.or_eq_true, decide_eq_true_eq] at here
  have step_ge := observationDistance_le_kantorovichStep (P := realChain P) (Q := realChain P)
    (c := (c : ℝ)) (fun u v => (dual.kernel u v : ℝ)) s t
  rcases here with (nonpos | ⟨i, observed⟩) | witnessed
  · have cast : (dual.kernel s t : ℝ) ≤ 0 := by exact_mod_cast nonpos
    exact cast.trans ((observationDistance_nonneg _ _ s t).trans step_ge)
  · have cast : (dual.kernel s t : ℝ) ≤ |(P.observe i s : ℝ) - (P.observe i t : ℝ)| := by
      exact_mod_cast observed
    exact cast.trans
      ((abs_observe_sub_le_observationDistance (realChain P) (realChain P) i s t).trans step_ge)
  · rcases listed : dual.witness s t with _ | ⟨a, f, g⟩
    · simp [listed] at witnessed
    · simp only [listed, Bool.and_eq_true, decide_eq_true_eq] at witnessed
      obtain ⟨potential, gain⟩ := witnessed
      have below : ∀ ω : Coupling ((realChain P).trans a s) ((realChain P).trans a t),
          expect ((realChain P).trans a s) (fun u => (f u : ℝ)) -
              expect ((realChain P).trans a t) (fun v => (g v : ℝ)) ≤
            ω.cost (fun u v => (dual.kernel u v : ℝ)) := by
        intro ω
        rw [ω.expect_sub_expect]
        unfold Coupling.cost
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left ?_ (ω.nonneg u v)
        have cast : ((f u - g v : ℚ) : ℝ) ≤ (dual.kernel u v : ℝ) := Rat.cast_le.mpr (potential u v)
        rw [Rat.cast_sub] at cast
        exact cast
      have lifted := le_kantorovich ((realChain P).isDistribution a s)
        ((realChain P).isDistribution a t) below
      have cast_gain := (Rat.cast_le (K := ℝ)).mpr gain
      rw [Rat.cast_mul, Rat.cast_sub, ← expect_realChain, ← expect_realChain] at cast_gain
      exact cast_gain.trans ((mul_le_mul_of_nonneg_left lifted (Rat.cast_nonneg.mpr c_nonneg)).trans
        (mul_kantorovich_le_kantorovichStep _ a s t))

/-- **Soundness of the dual checker**: acceptance implies kernel `≤` metric pointwise on the real
chain, at every discount `0 ≤ c < 1`. -/
theorem dualCheck_sound (accepted : dualCheck P c dual = true) (c_nonneg : 0 ≤ c) (c_lt : c < 1)
    (s t : S) :
    (dual.kernel s t : ℝ) ≤ bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t :=
  le_bisimulationMetric_of_le_step (m := fun u v => (dual.kernel u v : ℝ))
    (Rat.cast_nonneg.mpr c_nonneg) (by exact_mod_cast c_lt) (dualCheck_le_step accepted c_nonneg) s t

end Soundness

/-! ## With a prefixpoint: exact, or an interval -/

section Measurement

variable [Fintype A] [Fintype Atom] [DecidableEq S]

/-- **Measure the distance at a pair** from a prefixpoint and a dual post-fixpoint; nothing unless
both are accepted. -/
def measureByDual (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : Prefixpoint A S)
    (dual : DualPostfixpoint A S) (x y : S) : Option Measurement :=
  if check P c cert && dualCheck P c dual then some (measure (dual.kernel x y) (cert.kernel x y))
  else none

/-- **Decide "at most `ε`" at a pair** from a prefixpoint and a dual post-fixpoint; nothing unless
both are accepted. -/
def withinByDual (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : Prefixpoint A S)
    (dual : DualPostfixpoint A S) (x y : S) (ε : ℚ) : Option Verdict :=
  if check P c cert && dualCheck P c dual then some (within (dual.kernel x y) (cert.kernel x y) ε)
  else none

variable {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cert : Prefixpoint A S}
  {dual : DualPostfixpoint A S} {x y : S}

/-- **Exact when the two certificates meet**, at every discount `0 ≤ c < 1`. -/
theorem bisimulationMetric_eq_of_dual_meet (accepted : check P c cert = true)
    (accepted' : dualCheck P c dual = true) (meet : dual.kernel x y = cert.kernel x y)
    (c_nonneg : 0 ≤ c) (c_lt : c < 1) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y = (cert.kernel x y : ℝ) := by
  have below := dualCheck_sound accepted' c_nonneg c_lt x y
  rw [meet] at below
  exact le_antisymm (check_sound accepted c_nonneg x y) below

theorem measureByDual_some {m : Measurement} (measured : measureByDual P c cert dual x y = some m) :
    check P c cert = true ∧ dualCheck P c dual = true ∧
      m = measure (dual.kernel x y) (cert.kernel x y) := by
  unfold measureByDual at measured
  split_ifs at measured with accepted
  simp only [Bool.and_eq_true] at accepted
  exact ⟨accepted.1, accepted.2, (Option.some.inj measured).symm⟩

/-- **An exact measurement is the metric**, at every discount `0 ≤ c < 1`. -/
theorem measureByDual_exact {r : ℚ} (measured : measureByDual P c cert dual x y = some (.exact r))
    (c_nonneg : 0 ≤ c) (c_lt : c < 1) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y = (r : ℝ) := by
  obtain ⟨accepted, accepted', shape⟩ := measureByDual_some measured
  exact measure_exact (dualCheck_sound accepted' c_nonneg c_lt x y)
    (check_sound accepted c_nonneg x y) shape.symm

/-- **An interval brackets the metric and does not close**, at every discount `0 ≤ c < 1`. -/
theorem measureByDual_between {l u : ℚ}
    (measured : measureByDual P c cert dual x y = some (.between l u)) (c_nonneg : 0 ≤ c)
    (c_lt : c < 1) :
    l < u ∧ (l : ℝ) ≤ bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ∧
      bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ≤ (u : ℝ) := by
  obtain ⟨accepted, accepted', shape⟩ := measureByDual_some measured
  obtain ⟨rfl, rfl, lt, below, above⟩ := measure_between (dualCheck_sound accepted' c_nonneg c_lt x y)
    (check_sound accepted c_nonneg x y) shape.symm
  exact ⟨lt, below, above⟩

/-- **"Holds" and "fails" are sound**, at every discount `0 ≤ c < 1`. -/
theorem withinByDual_sound {ε : ℚ} {v : Verdict} (verdict : withinByDual P c cert dual x y ε = some v)
    (c_nonneg : 0 ≤ c) (c_lt : c < 1) :
    (v = .holds → bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ≤ (ε : ℝ)) ∧
      (v = .fails → (ε : ℝ) < bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y) := by
  unfold withinByDual at verdict
  split_ifs at verdict with accepted
  simp only [Bool.and_eq_true] at accepted
  have shape := (Option.some.inj verdict).symm
  refine ⟨fun holds => ?_, fun fails => ?_⟩
  · subst holds
    exact within_holds (check_sound accepted.1 c_nonneg x y) shape.symm
  · subst fails
    exact within_fails (dualCheck_sound accepted.2 c_nonneg c_lt x y) shape.symm

end Measurement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
