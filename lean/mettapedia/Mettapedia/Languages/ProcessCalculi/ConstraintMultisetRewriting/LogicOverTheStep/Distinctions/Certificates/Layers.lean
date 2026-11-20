import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Upper
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Lower

/-!
# Layered prefixpoints: a sequence of kernels bounds the depth-indexed distances

A claim about a horizon of `h` steps needs no fixed point: kernels `D 0, …, D h`, with `D 0` above
the observation distance and each `D (n + 1)` above the Kantorovich step of `D n`, bound the
iterates `0, …, h` (`approxMetric_le_of_steps`), at every discount `0 ≤ c`, the range in which the
step is monotone. As a certificate the step is witnessed by couplings (`LayeredBound`): for every
`n < h`, action and pair, a coupling whose discounted cost under `D n` is at most `D (n + 1)` at the
pair; then the iterates are below the layers (`LayeredBound.approxMetric_le`), and at
`0 ≤ c ≤ 1` so are the logical distances of tests of depth at most `n`
(`LayeredBound.depthDistance_le`, from `approxMetric_eq_depthDistance`).

**Existence and tightness.** A coupling bound is a constant layered bound at every horizon
(`layeredBound_const`); the iterates themselves are a layered bound with optimal couplings
(`layeredBound_approxMetric`), so they are the least one. A rational layered bound is a real one of
the real chains (`layeredBound_real`).

**The checker** (`layeredCheck`) of a layered certificate (`LayeredPrefixpoint`: layers up to a
horizon, and for each step listed couplings, omitted pairs filled in as for a prefixpoint, from one
layer to the next): acceptance makes the layers, with their diagonals set to zero, a layered bound
(`layeredCheck_layeredBound`), so every iterate up to the horizon is below its layer
(`layeredCheck_sound`) at every discount `0 ≤ c`, and so is the logical distance of tests of at most
that depth at `0 ≤ c ≤ 1` (`layeredCheck_depthDistance`). When a test of depth at most `n` meets
layer `n` at a pair, the `n`-th iterate there is exact (`approxMetric_eq_of_meet`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.GSLT.Distinction.Probabilistic

variable {A Atom S T : Type*} [Fintype S] [Fintype T]

/-- **A layered bound up to horizon `h`**: kernels `D 0, …, D h`, each nonnegative and bounding
every observation difference, and for every `n < h`, action and pair, a coupling of the successor
distributions whose discounted cost under `D n` is at most `D (n + 1)` at the pair. -/
structure LayeredBound {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (P : LabelledMarkovChain 𝕜 A Atom S) (Q : LabelledMarkovChain 𝕜 A Atom T) (c : 𝕜) (h : ℕ)
    (D : ℕ → S → T → 𝕜) : Prop where
  nonneg : ∀ n ≤ h, ∀ s t, 0 ≤ D n s t
  observe_le : ∀ n ≤ h, ∀ i s t, |P.observe i s - Q.observe i t| ≤ D n s t
  step_le : ∀ n < h, ∀ a s t,
    ∃ ω : Coupling (P.trans a s) (Q.trans a t), c * ω.cost (D n) ≤ D (n + 1) s t

/-- **A coupling bound is a constant layered bound**, at every horizon. -/
theorem layeredBound_const {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {P : LabelledMarkovChain 𝕜 A Atom S} {Q : LabelledMarkovChain 𝕜 A Atom T} {c : 𝕜}
    {m : S → T → 𝕜} (bound : CouplingBound P Q c m) (h : ℕ) :
    LayeredBound P Q c h fun _ => m :=
  ⟨fun _ _ => bound.nonneg, fun _ _ => bound.observe_le, fun _ _ => bound.step_le⟩

/-- **A rational layered bound is a real layered bound** of the real chains. -/
theorem layeredBound_real {P : LabelledMarkovChain ℚ A Atom S} {Q : LabelledMarkovChain ℚ A Atom T}
    {c : ℚ} {h : ℕ} {D : ℕ → S → T → ℚ} (bound : LayeredBound P Q c h D) :
    LayeredBound (realChain P) (realChain Q) (c : ℝ) h fun n s t => (D n s t : ℝ) where
  nonneg n le s t := Rat.cast_nonneg.mpr (bound.nonneg n le s t)
  observe_le n le i s t := by
    have close := bound.observe_le n le i s t
    change |(P.observe i s : ℝ) - (Q.observe i t : ℝ)| ≤ (D n s t : ℝ)
    exact_mod_cast close
  step_le n lt a s t := by
    obtain ⟨ω, le⟩ := bound.step_le n lt a s t
    refine ⟨realCoupling ω, ?_⟩
    have cast_le : ((c * ω.cost (D n) : ℚ) : ℝ) ≤ (D (n + 1) s t : ℝ) := Rat.cast_le.mpr le
    rw [Rat.cast_mul] at cast_le
    calc (c : ℝ) * (realCoupling ω).cost (fun s t => (D n s t : ℝ))
        = (c : ℝ) * (ω.cost (D n) : ℝ) := by rw [cost_realCoupling]
      _ ≤ (D (n + 1) s t : ℝ) := cast_le

section RealLayers

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℝ A Atom S}
  {Q : LabelledMarkovChain ℝ A Atom T} {c : ℝ} {h : ℕ}

/-- **Kernels each above the step of the previous bound the iterates**: if `D 0` is above the
observation distance and `D (n + 1)` above the Kantorovich step of `D n` for every `n < h`, then the
`n`-th iterate is below `D n` for every `n ≤ h`, at every discount `0 ≤ c`. -/
theorem approxMetric_le_of_steps {D : ℕ → S → T → ℝ} (c_nonneg : 0 ≤ c)
    (base : ∀ s t, observationDistance P Q s t ≤ D 0 s t)
    (step : ∀ n < h, ∀ s t, kantorovichStep P Q c (D n) s t ≤ D (n + 1) s t) :
    ∀ n ≤ h, ∀ s t, approxMetric P Q c n s t ≤ D n s t := by
  intro n
  induction n with
  | zero => intro _ s t; exact base s t
  | succ n ih =>
      intro le s t
      exact (kantorovichStep_mono c_nonneg (ih (by omega)) s t).trans (step n (by omega) s t)

/-- **A layered bound bounds the iterates**, at every discount `0 ≤ c`. -/
theorem LayeredBound.approxMetric_le {D : ℕ → S → T → ℝ} (bound : LayeredBound P Q c h D)
    (c_nonneg : 0 ≤ c) : ∀ n ≤ h, ∀ s t, approxMetric P Q c n s t ≤ D n s t :=
  approxMetric_le_of_steps c_nonneg
    (fun s t => (observationDistance_le_iff P Q).mpr
      ⟨bound.nonneg 0 (Nat.zero_le h) s t, fun i => bound.observe_le 0 (Nat.zero_le h) i s t⟩)
    (fun n lt s t => kantorovichStep_le_iff.mpr
      ⟨(observationDistance_le_iff P Q).mpr
          ⟨bound.nonneg (n + 1) lt s t, fun i => bound.observe_le (n + 1) lt i s t⟩,
        fun a => by
          obtain ⟨ω, le⟩ := bound.step_le n lt a s t
          exact (mul_le_mul_of_nonneg_left (kantorovich_le (P.isDistribution a s) (D n) ω)
            c_nonneg).trans le⟩)

/-- **A layered bound bounds the logical distance of tests of at most each depth**, at every
discount `0 ≤ c ≤ 1`. -/
theorem LayeredBound.depthDistance_le {P : LabelledMarkovChain ℝ A Atom S} {D : ℕ → S → S → ℝ}
    (bound : LayeredBound P P c h D) (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    ∀ n ≤ h, ∀ s t, distanceOver P c (depthAtMost n) s t ≤ D n s t := by
  intro n le s t
  rw [← approxMetric_eq_depthDistance c_nonneg c_le]
  exact bound.approxMetric_le c_nonneg n le s t

/-- **The iterates are a layered bound**, with optimal couplings, at every horizon; with
`LayeredBound.approxMetric_le` they are the least one. -/
theorem layeredBound_approxMetric (h : ℕ) : LayeredBound P Q c h (approxMetric P Q c) where
  nonneg n _ s t := approxMetric_nonneg n s t
  observe_le n _ i s t := by
    cases n with
    | zero => exact abs_observe_sub_le_observationDistance P Q i s t
    | succ n =>
        exact (abs_observe_sub_le_observationDistance P Q i s t).trans
          (observationDistance_le_kantorovichStep _ s t)
  step_le n _ a s t := by
    obtain ⟨ω, optimal⟩ :=
      exists_optimal_coupling (P.isDistribution a s) (Q.isDistribution a t) (approxMetric P Q c n)
    exact ⟨ω, by rw [optimal]; exact mul_kantorovich_le_kantorovichStep _ a s t⟩

end RealLayers

/-! ## A checker for layered certificates -/

/-- **A layered certificate** up to a horizon: kernels for the layers and, for each step `n` before
the horizon, listed couplings from layer `n` to layer `n + 1`; omitted pairs are filled in as for a
prefixpoint. -/
structure LayeredPrefixpoint (A S : Type*) where
  /-- The horizon. -/
  horizon : ℕ
  /-- The layers. -/
  layer : ℕ → S → S → ℚ
  /-- The listed couplings of each step. -/
  listed : ℕ → A → S → S → Option (S → S → ℚ)

section LayeredChecker

variable [DecidableEq S] [Fintype A] [Fintype Atom]

/-- **The checker** of layered certificates: every layer up to the horizon is nonnegative and bounds
every observation difference, and every step before the horizon is covered from its layer to the
next. -/
def layeredCheck (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : LayeredPrefixpoint A S) :
    Bool :=
  decide (∀ n, n ≤ cert.horizon → ∀ s t, 0 ≤ cert.layer n s t) &&
    decide (∀ n, n ≤ cert.horizon → ∀ i s t, |P.observe i s - P.observe i t| ≤ cert.layer n s t) &&
    decide (∀ n, n < cert.horizon → ∀ a s t,
      coveredBetween P c (cert.layer n) (cert.layer (n + 1)) (cert.listed n) a s t = true)

variable {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cert : LayeredPrefixpoint A S}

theorem layeredCheck_iff :
    layeredCheck P c cert = true ↔
      (∀ n, n ≤ cert.horizon → ∀ s t, 0 ≤ cert.layer n s t) ∧
        (∀ n, n ≤ cert.horizon → ∀ i s t, |P.observe i s - P.observe i t| ≤ cert.layer n s t) ∧
          ∀ n, n < cert.horizon → ∀ a s t,
            coveredBetween P c (cert.layer n) (cert.layer (n + 1)) (cert.listed n) a s t = true := by
  simp only [layeredCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- **The accepted layers, with their diagonals set to zero, are a layered bound** of the rational
chain with itself, at every discount `0 ≤ c`. -/
theorem layeredCheck_layeredBound (accepted : layeredCheck P c cert = true) (c_nonneg : 0 ≤ c) :
    LayeredBound P P c cert.horizon fun n => offDiagonal (cert.layer n) := by
  obtain ⟨nonneg, observed, covered⟩ := layeredCheck_iff.mp accepted
  refine ⟨fun n le s t => ?_, fun n le i s t => ?_, fun n lt a s t => ?_⟩
  · unfold offDiagonal
    split_ifs
    · exact le_rfl
    · exact nonneg n le s t
  · unfold offDiagonal
    split_ifs with same
    · subst same
      simp
    · exact observed n le i s t
  · by_cases same : s = t
    · subst same
      refine ⟨Coupling.diagonal (P.isDistribution a s), ?_⟩
      have zero :
          (Coupling.diagonal (P.isDistribution a s)).cost (offDiagonal (cert.layer n)) = 0 := by
        unfold Coupling.cost
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        change (if x = y then P.trans a s x else 0) * (if x = y then 0 else cert.layer n x y) = 0
        split_ifs <;> simp
      rw [zero, mul_zero]
      simp [offDiagonal]
    · obtain ⟨ω, le⟩ := exists_coupling_of_coveredBetween (covered n lt) a same
      refine ⟨ω, ?_⟩
      rw [show offDiagonal (cert.layer (n + 1)) s t = cert.layer (n + 1) s t by
        simp [offDiagonal, same]]
      have below : ∀ u v, offDiagonal (cert.layer n) u v ≤ cert.layer n u v := fun u v => by
        unfold offDiagonal
        split_ifs with equal
        · subst equal
          exact nonneg n lt.le u u
        · exact le_rfl
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono below) c_nonneg).trans le

/-- **Soundness of the layered checker**: every iterate up to the horizon is below its layer, on the
real chain, at every discount `0 ≤ c`. -/
theorem layeredCheck_sound (accepted : layeredCheck P c cert = true) (c_nonneg : 0 ≤ c) :
    ∀ n ≤ cert.horizon, ∀ s t,
      approxMetric (realChain P) (realChain P) (c : ℝ) n s t ≤ (cert.layer n s t : ℝ) := by
  intro n le s t
  have bound := (layeredBound_real (layeredCheck_layeredBound accepted c_nonneg)).approxMetric_le
    (Rat.cast_nonneg.mpr c_nonneg) n le s t
  refine bound.trans (Rat.cast_le.mpr ?_)
  unfold offDiagonal
  split_ifs with same
  · subst same
    exact (layeredCheck_iff.mp accepted).1 n le s s
  · exact le_rfl

/-- **The logical distance of tests of at most each depth is below its layer**, at every discount
`0 ≤ c ≤ 1`. -/
theorem layeredCheck_depthDistance (accepted : layeredCheck P c cert = true) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) :
    ∀ n ≤ cert.horizon, ∀ s t,
      distanceOver (realChain P) (c : ℝ) (depthAtMost n) s t ≤ (cert.layer n s t : ℝ) := by
  intro n le s t
  rw [← approxMetric_eq_depthDistance (Rat.cast_nonneg.mpr c_nonneg) (by exact_mod_cast c_le)]
  exact layeredCheck_sound accepted c_nonneg n le s t

/-- **Exact at a horizon when a test meets the layer**: if a test of depth at most `n` has at a pair
the value of layer `n` there, the `n`-th iterate at that pair is that rational, at every discount
`0 ≤ c`. -/
theorem approxMetric_eq_of_meet (accepted : layeredCheck P c cert = true)
    {nodes : List (TestNode A Atom)} {x y : S} {g : ℚ} {d n : ℕ}
    (gap : testGap P c nodes x y = some (g, d)) (deep : d ≤ n) (within : n ≤ cert.horizon)
    (meet : g = cert.layer n x y) (c_nonneg : 0 ≤ c) :
    approxMetric (realChain P) (realChain P) (c : ℝ) n x y = (g : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [meet]
    exact layeredCheck_sound accepted c_nonneg n within x y
  · exact (testGap_le_approxMetric gap c_nonneg).trans
      (approxMetric_mono (Rat.cast_nonneg.mpr c_nonneg) x y deep)

end LayeredChecker

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
