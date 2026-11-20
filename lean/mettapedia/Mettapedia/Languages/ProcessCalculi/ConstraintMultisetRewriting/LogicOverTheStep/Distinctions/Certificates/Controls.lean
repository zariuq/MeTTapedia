import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Dual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Layers

/-!
# Controls: the checkers on a leaking chain, by kernel evaluation

**The leak chain** (`leak`): four states, one action, one indicator observation (of the sink).
State `0` (safe) stays; `1` (once) moves to `0` or to the sink `3`, each with probability `1/2`;
`2` (leaky) stays or falls into the sink, each with probability `1/2`; the sink stays. At discount
`9/10` its metric is `exactKernel`: `9/20` between `0` and `1`, `9/11` between `0` and `2` (the
fixed point of `d = (9/10)(d + 1)/2`), `81/220` between `1` and `2`, and `1` against the sink.

**The upper checker.**
* Accepted (`correct_accepted`): the exact kernel with one listed coupling, at the pair `(1, 2)`;
  every other pair is filled in by the checker.
* Refused, each wrong in exactly one way:
  - a listed table with a wrong marginal, whose cost is within the kernel (`wrongMarginal_refused`,
    `wrongMarginal_fault`);
  - the kernel too small at one pair, `1/3` at `(1, 2)` and `(2, 1)` (`tooSmall_refused`,
    `tooSmall_fault`); the claim is false (`tooSmall_wrong`);
  - the coupling of `(1, 2)` missing, which no fill-in replaces (`missing_refused`,
    `missing_fault`); its kernel is the metric, so this is missing evidence, not a false claim;
  - an asymmetric kernel, `1` at `(2, 1)` (`asymmetric_refused`); the soundness conditions accept it
    (`asymmetric_core_accepted`), so the refusal is the shape's alone, and its bound is sound.

**Tests.** The depth-one test "the sink next" meets the kernel at `(0, 1)`: the measurement is exact,
`9/20` (`measure_once`, `metric_safe_once`). At `(0, 2)` the depth-two test with a shared node gives
`261/400`, an interval (`measure_two`); "at most `1/2`" fails, "at most `4/5`" is not decided. No
test of any depth closes the interval at `(0, 2)`: every test's gap there is below `9/11`
(`eval_gap_lt`, `testGap_lt`), so a measurement by tests is never exact there
(`measureByTest_never_exact`). A test citing a later node is refused (`testForward_refused`).

**The dual certificate** with the potential `(0, -9/20, -9/11, -1)` is accepted
(`exactDual_accepted`); with the upper certificate the metric is exact everywhere
(`bisimulationMetric_leak`), in particular `9/11` between `0` and `2` (`metric_safe_leaky`), and
"at most `4/5`" fails there (`within_dual_fails`).

**At discount one** (`loops`: two self-loops, one observation): the upper checker accepts the zero
kernel and the dual checker accepts the kernel one off the diagonal (`zeroCert_accepted`,
`stuckDual_accepted`), so that kernel is a post-fixpoint above the metric
(`postfixpoint_above_metric_at_one`): the dual lemma's hypothesis `c < 1` cannot be dropped.

**Layers up to horizon two** (`layers`): the observation distance, then `9/20` and `261/400` at the
leak pair. Accepted (`layers_accepted`); the depth-two test meets the second layer, so the horizon-two
distance at the leak pair is exactly `261/400` (`approxMetric_two_safe_leaky`). The first layer
lowered to `2/5` at the leak pair is refused (`smallLayers_refused`), and that claim is false: the
depth-one test already gives `9/20` there (`smallLayers_wrong`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls

open Mettapedia.Cybernetics.ApproximateAdequacy
open FunctionalExpression

/-! ## The leak chain -/

/-- The successor distributions: `0` stays; `1` moves to `0` or `3`; `2` stays or moves to `3`; `3`
stays. -/
def leakTrans : Fin 4 → Fin 4 → ℚ :=
  ![![1, 0, 0, 0], ![1 / 2, 0, 0, 1 / 2], ![0, 0, 1 / 2, 1 / 2], ![0, 0, 0, 1]]

theorem leakTrans_nonneg : ∀ s x, 0 ≤ leakTrans s x := by decide +kernel

theorem leakTrans_total : ∀ s, ∑ x, leakTrans s x = 1 := by decide +kernel

/-- **The leak chain**: one action; one indicator observation, of the sink `3`. -/
def leak : LabelledMarkovChain ℚ Unit Unit (Fin 4) where
  trans _ := leakTrans
  isDistribution _ s := ⟨leakTrans_nonneg s, leakTrans_total s⟩
  observe _ := ![0, 0, 0, 1]

/-- The discount. -/
def discount : ℚ := 9 / 10

theorem discount_nonneg : 0 ≤ discount := by norm_num [discount]

theorem discount_lt_one : discount < 1 := by norm_num [discount]

theorem discount_real : ((discount : ℚ) : ℝ) = 9 / 10 := by norm_num [discount]

/-- The metric of the leak chain at discount `9/10`. -/
def exactKernel : Fin 4 → Fin 4 → ℚ :=
  ![![0, 9 / 20, 9 / 11, 1], ![9 / 20, 0, 81 / 220, 1], ![9 / 11, 81 / 220, 0, 1], ![1, 1, 1, 0]]

/-- The coupling of `1` and `2`: `0` with `2`, and the sink with itself. -/
def onceLeaky : Fin 4 → Fin 4 → ℚ :=
  ![![0, 0, 1 / 2, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1 / 2]]

/-- List a table at the pair `(1, 2)` only. -/
def listedAt12 (θ : Fin 4 → Fin 4 → ℚ) : Unit → Fin 4 → Fin 4 → Option (Fin 4 → Fin 4 → ℚ) :=
  fun _ s t => if s = 1 ∧ t = 2 then some θ else none

/-! ## The upper checker: one acceptance, four refusals -/

/-- **The correct certificate**: the exact kernel, one listed coupling. -/
def correct : Prefixpoint Unit (Fin 4) := ⟨exactKernel, listedAt12 onceLeaky⟩

theorem correct_accepted : check leak discount correct = true := by decide +kernel

/-- A table with a wrong marginal: the sink row carries `1/4` instead of `1/2`. -/
def badTable : Fin 4 → Fin 4 → ℚ :=
  ![![0, 0, 1 / 2, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1 / 4]]

def wrongMarginal : Prefixpoint Unit (Fin 4) := ⟨exactKernel, listedAt12 badTable⟩

theorem wrongMarginal_refused : check leak discount wrongMarginal = false := by decide +kernel

/-- Its only fault: the table is not a coupling; its cost is within the kernel. -/
theorem wrongMarginal_fault :
    ¬ IsCouplingTable (leakTrans 1) (leakTrans 2) badTable ∧
      discount * jointCost badTable exactKernel ≤ exactKernel 1 2 := by decide +kernel

/-- The exact kernel with `1/3` at `(1, 2)` and `(2, 1)`. -/
def smallKernel : Fin 4 → Fin 4 → ℚ :=
  ![![0, 9 / 20, 9 / 11, 1], ![9 / 20, 0, 1 / 3, 1], ![9 / 11, 1 / 3, 0, 1], ![1, 1, 1, 0]]

def tooSmall : Prefixpoint Unit (Fin 4) := ⟨smallKernel, listedAt12 onceLeaky⟩

theorem tooSmall_refused : check leak discount tooSmall = false := by decide +kernel

/-- Its only fault: the coupling is right, its discounted cost exceeds the kernel at the pair. -/
theorem tooSmall_fault :
    IsCouplingTable (leakTrans 1) (leakTrans 2) onceLeaky ∧
      ¬ discount * jointCost onceLeaky smallKernel ≤ smallKernel 1 2 := by decide +kernel

/-- The exact kernel with no listed coupling. -/
def missing : Prefixpoint Unit (Fin 4) := ⟨exactKernel, fun _ _ _ => none⟩

theorem missing_refused : check leak discount missing = false := by decide +kernel

/-- Its only fault: the pairs `(1, 2)` and `(2, 1)` are not covered, every other pair is filled in,
and the shape holds. -/
theorem missing_fault :
    coveredAt leak discount missing () 1 2 = false ∧ coveredAt leak discount missing () 2 1 = false ∧
      (∀ s t : Fin 4, ¬ (s = 1 ∧ t = 2) → ¬ (s = 2 ∧ t = 1) →
        coveredAt leak discount missing () s t = true) ∧
      shapeCheck missing = true := by decide +kernel

/-- The exact kernel with `1` at `(2, 1)`. -/
def asymmetricKernel : Fin 4 → Fin 4 → ℚ :=
  ![![0, 9 / 20, 9 / 11, 1], ![9 / 20, 0, 81 / 220, 1], ![9 / 11, 1, 0, 1], ![1, 1, 1, 0]]

def asymmetric : Prefixpoint Unit (Fin 4) := ⟨asymmetricKernel, listedAt12 onceLeaky⟩

theorem asymmetric_refused : check leak discount asymmetric = false := by decide +kernel

/-- **The refusal is the shape's alone**: the soundness conditions accept it. -/
theorem asymmetric_core_accepted : coreCheck leak discount asymmetric = true := by decide +kernel

/-! ## The dual certificate and the exact metric -/

/-- The potential `u ↦ -metric(0, u)`. -/
def potential : Fin 4 → ℚ := ![0, -(9 / 20), -(9 / 11), -1]

/-- **The dual certificate**: the exact kernel, with the potential on the pairs `(0, 1)`, `(0, 2)`,
`(1, 2)` and its negative on their reverses; the other pairs are justified by an observation or by
a zero kernel. -/
def exactDual : DualPostfixpoint Unit (Fin 4) where
  kernel := exactKernel
  witness s t :=
    if s < t ∧ t ≠ 3 then some ((), potential, potential)
    else if t < s ∧ s ≠ 3 then some ((), fun u => -potential u, fun u => -potential u)
    else none

theorem exactDual_accepted : dualCheck leak discount exactDual = true := by decide +kernel

/-- **The metric of the leak chain at discount `9/10` is `exactKernel`**, at every pair: the two
certificates meet everywhere. -/
theorem bisimulationMetric_leak (s t : Fin 4) :
    bisimulationMetric (realChain leak) (realChain leak) (discount : ℝ) s t = (exactKernel s t : ℝ) :=
  bisimulationMetric_eq_of_dual_meet (cert := correct) correct_accepted exactDual_accepted rfl
    discount_nonneg discount_lt_one

/-- **`9/11` between the safe and the leaky state.** -/
theorem metric_safe_leaky :
    bisimulationMetric (realChain leak) (realChain leak) (9 / 10) 0 2 = 9 / 11 := by
  have value : exactKernel 0 2 = 9 / 11 := by decide +kernel
  rw [← discount_real, bisimulationMetric_leak, value]
  norm_num

theorem measure_dual :
    measureByDual leak discount correct exactDual 0 2 = some (.exact (9 / 11)) := by decide +kernel

theorem within_dual_fails :
    withinByDual leak discount correct exactDual 0 2 (4 / 5) = some .fails := by decide +kernel

/-- **The claim of `tooSmall` is false**: the metric at `(1, 2)` exceeds `1/3`. -/
theorem tooSmall_wrong :
    (smallKernel 1 2 : ℝ) < bisimulationMetric (realChain leak) (realChain leak) (discount : ℝ) 1 2 := by
  have small : smallKernel 1 2 = 1 / 3 := by decide +kernel
  have exact : exactKernel 1 2 = 81 / 220 := by decide +kernel
  rw [bisimulationMetric_leak, small, exact]
  norm_num

/-- **The kernel of `missing` is the metric**: its refusal is for missing evidence. -/
theorem missing_kernel_is_metric (s t : Fin 4) :
    bisimulationMetric (realChain leak) (realChain leak) (discount : ℝ) s t = (missing.kernel s t : ℝ) :=
  bisimulationMetric_leak s t

/-! ## Tests -/

/-- "The sink next": depth one. -/
def testOnce : List (TestNode Unit Unit) := [.observe (), .next () 0]

/-- "Next, the sink or the sink next": depth two, the observation node shared. -/
def testTwo : List (TestNode Unit Unit) := [.observe (), .next () 0, .max 0 1, .next () 2]

/-- A node citing a later node. -/
def testForward : List (TestNode Unit Unit) := [.next () 1, .observe ()]

theorem testOnce_gap : testGap leak discount testOnce 0 1 = some (9 / 20, 1) := by decide +kernel

theorem testTwo_gap : testGap leak discount testTwo 0 2 = some (261 / 400, 2) := by decide +kernel

theorem testForward_refused : testGap leak discount testForward 0 1 = none := by decide +kernel

theorem measure_once : measureByTest leak discount correct testOnce 0 1 = some (.exact (9 / 20)) := by
  decide +kernel

/-- **Exact at `(0, 1)` by a test meeting the prefixpoint.** -/
theorem metric_safe_once :
    bisimulationMetric (realChain leak) (realChain leak) (9 / 10) 0 1 = 9 / 20 := by
  have exact := measureByTest_exact measure_once discount_nonneg discount_lt_one.le
  rw [discount_real] at exact
  rw [exact]
  norm_num

theorem measure_two :
    measureByTest leak discount correct testTwo 0 2 = some (.between (261 / 400) (9 / 11)) := by
  decide +kernel

theorem within_once_holds : withinByTest leak discount correct testOnce 0 1 (1 / 2) = some .holds := by
  decide +kernel

theorem within_two_fails : withinByTest leak discount correct testTwo 0 2 (1 / 2) = some .fails := by
  decide +kernel

theorem within_two_undecided :
    withinByTest leak discount correct testTwo 0 2 (4 / 5) = some .undecided := by
  decide +kernel

/-! ## No test closes the interval at the leak pair -/

/-- The iterates between the leaky and the safe state stay below `9/11`, by
`(9/11)(1 - (9/20)^n)`. -/
theorem approxMetric_leaky_safe (n : ℕ) :
    approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 2 0 ≤
      9 / 11 * (1 - (9 / 20) ^ n) := by
  have c_nonneg : (0 : ℝ) ≤ (discount : ℝ) := Rat.cast_nonneg.mpr discount_nonneg
  have bound := couplingBound_real
    (coreCheck_couplingBound (check_iff.mp correct_accepted).1 discount_nonneg)
  have sink_safe : ∀ k, approxMetric (realChain leak) (realChain leak) (discount : ℝ) k 3 0 ≤ 1 := by
    intro k
    have below := approxMetric_le bound c_nonneg k 3 0
    have value : offDiagonal correct.kernel 3 0 = 1 := by decide +kernel
    have cast : ((offDiagonal correct.kernel 3 0 : ℚ) : ℝ) = 1 := by rw [value, Rat.cast_one]
    exact below.trans cast.le
  induction n with
  | zero =>
      change observationDistance (realChain leak) (realChain leak) 2 0 ≤ _
      refine (observationDistance_le_iff _ _).mpr ⟨by norm_num, fun i => ?_⟩
      simp [leak]
  | succ n ih =>
      change kantorovichStep (realChain leak) (realChain leak) (discount : ℝ)
        (approxMetric (realChain leak) (realChain leak) (discount : ℝ) n) 2 0 ≤ _
      have power : (9 / 20 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have target_nonneg : (0 : ℝ) ≤ 9 / 11 * (1 - (9 / 20) ^ (n + 1)) := by nlinarith
      refine kantorovichStep_le_iff.mpr
        ⟨(observationDistance_le_iff _ _).mpr ⟨target_nonneg, fun i => ?_⟩, fun a => ?_⟩
      · simpa [leak] using target_nonneg
      · have lifted := kantorovich_le ((realChain leak).isDistribution a 2)
          (approxMetric (realChain leak) (realChain leak) (discount : ℝ) n)
          (Coupling.independent ((realChain leak).isDistribution a 2)
            ((realChain leak).isDistribution a 0))
        have cost : (Coupling.independent ((realChain leak).isDistribution a 2)
            ((realChain leak).isDistribution a 0)).cost
              (approxMetric (realChain leak) (realChain leak) (discount : ℝ) n) =
            1 / 2 * approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 2 0 +
              1 / 2 * approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 3 0 := by
          simp [Coupling.cost, Coupling.independent, Fin.sum_univ_four, leak, leakTrans]
        rw [cost] at lifted
        have key : ∀ x y : ℝ, x ≤ 9 / 11 * (1 - (9 / 20) ^ n) → y ≤ 1 →
            (9 / 10 : ℝ) * (1 / 2 * x + 1 / 2 * y) ≤ 9 / 11 * (1 - (9 / 20) ^ (n + 1)) := by
          intro x y hx hy
          have identity : (9 / 10 : ℝ) * (1 / 2 * (9 / 11 * (1 - (9 / 20) ^ n)) + 1 / 2 * 1) =
              9 / 11 * (1 - (9 / 20) ^ (n + 1)) := by ring
          linarith
        calc (discount : ℝ) * kantorovich
              (approxMetric (realChain leak) (realChain leak) (discount : ℝ) n)
              ((realChain leak).trans a 2) ((realChain leak).trans a 0)
            ≤ (discount : ℝ) *
                (1 / 2 * approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 2 0 +
                  1 / 2 * approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 3 0) :=
              mul_le_mul_of_nonneg_left lifted c_nonneg
          _ = 9 / 10 *
                (1 / 2 * approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 2 0 +
                  1 / 2 * approxMetric (realChain leak) (realChain leak) (discount : ℝ) n 3 0) := by
              rw [discount_real]
          _ ≤ 9 / 11 * (1 - (9 / 20) ^ (n + 1)) := key _ _ ih (sink_safe n)

/-- **Every test's gap between the safe and the leaky state is below `9/11`.** -/
theorem eval_gap_lt (φ : FunctionalExpression ℚ Unit Unit) :
    |φ.eval leak discount 0 - φ.eval leak discount 2| < 9 / 11 := by
  have bound := abs_eval_sub_le_approxMetric_real leak leak discount_nonneg φ le_rfl 2 0
  have chain := approxMetric_leaky_safe φ.depth
  have power : (0 : ℝ) < (9 / 20 : ℝ) ^ φ.depth := pow_pos (by norm_num) _
  have real : ((|φ.eval leak discount 2 - φ.eval leak discount 0| : ℚ) : ℝ) < ((9 / 11 : ℚ) : ℝ) := by
    have nine : ((9 / 11 : ℚ) : ℝ) = 9 / 11 := by norm_num
    rw [nine]
    linarith
  rw [abs_sub_comm]
  exact_mod_cast real

/-- **No test DAG reaches `9/11` at the leak pair.** -/
theorem testGap_lt {nodes : List (TestNode Unit Unit)} {g : ℚ} {d : ℕ}
    (gap : testGap leak discount nodes 0 2 = some (g, d)) : g < 9 / 11 := by
  obtain ⟨φ, _, rfl⟩ := testGap_represents gap
  exact eval_gap_lt φ

/-- **A measurement by tests is never exact at the leak pair**: the interval stays open, and is
never read as a refutation. -/
theorem measureByTest_never_exact (nodes : List (TestNode Unit Unit)) (r : ℚ) :
    measureByTest leak discount correct nodes 0 2 ≠ some (.exact r) := by
  intro measured
  obtain ⟨_, g, d, gap, shape⟩ := measureByTest_some measured
  have lt := testGap_lt gap
  unfold measure at shape
  split_ifs at shape with meet
  have upper : correct.kernel 0 2 = 9 / 11 := by decide +kernel
  rw [meet, upper] at lt
  exact lt_irrefl _ lt

/-! ## Layers up to horizon two -/

/-- The observation distance. -/
def layer0 : Fin 4 → Fin 4 → ℚ :=
  ![![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![1, 1, 1, 0]]

/-- The first iterate. -/
def layer1 : Fin 4 → Fin 4 → ℚ :=
  ![![0, 9 / 20, 9 / 20, 1], ![9 / 20, 0, 0, 1], ![9 / 20, 0, 0, 1], ![1, 1, 1, 0]]

/-- The second iterate. -/
def layer2 : Fin 4 → Fin 4 → ℚ :=
  ![![0, 9 / 20, 261 / 400, 1], ![9 / 20, 0, 81 / 400, 1], ![261 / 400, 81 / 400, 0, 1],
    ![1, 1, 1, 0]]

/-- **The layers of the leak chain up to horizon two**, with the coupling of `(1, 2)` listed at each
step. -/
def layers : LayeredPrefixpoint Unit (Fin 4) where
  horizon := 2
  layer n := if n = 0 then layer0 else if n = 1 then layer1 else layer2
  listed _ := listedAt12 onceLeaky

theorem layers_accepted : layeredCheck leak discount layers = true := by decide +kernel

theorem layers_meet : (261 / 400 : ℚ) = layers.layer 2 0 2 := by decide +kernel

/-- **The horizon-two distance at the leak pair is exactly `261/400`**: the depth-two test meets the
second layer. -/
theorem approxMetric_two_safe_leaky :
    approxMetric (realChain leak) (realChain leak) (discount : ℝ) 2 0 2 = ((261 / 400 : ℚ) : ℝ) :=
  approxMetric_eq_of_meet layers_accepted testTwo_gap le_rfl le_rfl layers_meet discount_nonneg

/-- The first layer lowered to `2/5` at the leak pair. -/
def smallLayer1 : Fin 4 → Fin 4 → ℚ :=
  ![![0, 9 / 20, 2 / 5, 1], ![9 / 20, 0, 0, 1], ![2 / 5, 0, 0, 1], ![1, 1, 1, 0]]

def smallLayers : LayeredPrefixpoint Unit (Fin 4) where
  horizon := 2
  layer n := if n = 0 then layer0 else if n = 1 then smallLayer1 else layer2
  listed _ := listedAt12 onceLeaky

theorem smallLayers_refused : layeredCheck leak discount smallLayers = false := by decide +kernel

theorem testOnce_gap_leak : testGap leak discount testOnce 0 2 = some (9 / 20, 1) := by
  decide +kernel

/-- **The claim of `smallLayers` is false**: the first iterate at the leak pair is at least `9/20`. -/
theorem smallLayers_wrong :
    ((smallLayer1 0 2 : ℚ) : ℝ) < approxMetric (realChain leak) (realChain leak) (discount : ℝ) 1 0 2 := by
  have below := testGap_le_approxMetric testOnce_gap_leak discount_nonneg
  have small : smallLayer1 0 2 = 2 / 5 := by decide +kernel
  rw [small]
  have half : ((9 / 20 : ℚ) : ℝ) = 9 / 20 := by norm_num
  have fifth : ((2 / 5 : ℚ) : ℝ) = 2 / 5 := by norm_num
  rw [half] at below
  rw [fifth]
  linarith

/-! ## At discount one a post-fixpoint lies above the metric -/

/-- Two self-loops. -/
def loopsTrans : Fin 2 → Fin 2 → ℚ := ![![1, 0], ![0, 1]]

theorem loopsTrans_nonneg : ∀ s x, 0 ≤ loopsTrans s x := by decide +kernel

theorem loopsTrans_total : ∀ s, ∑ x, loopsTrans s x = 1 := by decide +kernel

/-- **Two self-loops with the same observation.** -/
def loops : LabelledMarkovChain ℚ Unit Unit (Fin 2) where
  trans _ := loopsTrans
  isDistribution _ s := ⟨loopsTrans_nonneg s, loopsTrans_total s⟩
  observe _ _ := 0

/-- The zero kernel, every pair filled in. -/
def zeroCert : Prefixpoint Unit (Fin 2) := ⟨fun _ _ => 0, fun _ _ _ => none⟩

theorem zeroCert_accepted : check loops 1 zeroCert = true := by decide +kernel

/-- The indicator of a state. -/
def indicatorOf (s : Fin 2) : Fin 2 → ℚ := fun u => if u = s then 1 else 0

/-- **The kernel one off the diagonal, as a dual certificate at discount one.** -/
def stuckDual : DualPostfixpoint Unit (Fin 2) where
  kernel s t := if s = t then 0 else 1
  witness s t := if s = t then none else some ((), indicatorOf s, indicatorOf s)

theorem stuckDual_accepted : dualCheck loops 1 stuckDual = true := by decide +kernel

/-- **At discount one a post-fixpoint lies above the metric**: the kernel one off the diagonal is a
post-fixpoint of the two self-loops, and the metric between them is zero. -/
theorem postfixpoint_above_metric_at_one :
    (∀ s t, (stuckDual.kernel s t : ℝ) ≤ kantorovichStep (realChain loops) (realChain loops)
      ((1 : ℚ) : ℝ) (fun u v => (stuckDual.kernel u v : ℝ)) s t) ∧
      bisimulationMetric (realChain loops) (realChain loops) ((1 : ℚ) : ℝ) 0 1 <
        (stuckDual.kernel 0 1 : ℝ) := by
  refine ⟨dualCheck_le_step stuckDual_accepted zero_le_one, ?_⟩
  have upper := check_sound zeroCert_accepted zero_le_one 0 1
  have zero : ((zeroCert.kernel 0 1 : ℚ) : ℝ) = 0 := by simp [zeroCert]
  have one : ((stuckDual.kernel 0 1 : ℚ) : ℝ) = 1 := by norm_num [stuckDual]
  rw [one]
  linarith

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls
