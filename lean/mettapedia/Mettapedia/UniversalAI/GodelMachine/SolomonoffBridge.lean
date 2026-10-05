import Mettapedia.UniversalAI.GodelMachine.SelfImprovement
import Mettapedia.UniversalAI.ValueUnderIgnorance
import Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge
import Mettapedia.UniversalAI.SolomonoffPrior
import Mettapedia.UniversalAI.SolomonoffInduction

/-!
# Fixed mixture models for proof-based self-modification

The prediction model is the existing complexity-weighted mixture of lower
semicomputable semimeasures. Output completeness supplies its Kraft bound;
effective reference machines give concrete instances. History-percept encodings
select prefix scores, without claiming they are normalized conditional laws.

The policy results below inherit exact policy optimality and sound modification
from the generic agent layer. Their utility tolerance is explicit data, and is
not identified with environmental Kolmogorov complexity.
-/

namespace Mettapedia.UniversalAI.GodelMachine.SolomonoffBridge

open SelfModification BayesianAgents Classical
open Mettapedia.UniversalAI.SolomonoffPrior
open Mettapedia.UniversalAI.SolomonoffInduction
open Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge

/-! ## Part 1: Solomonoff Environment Model

The Solomonoff prior M provides a universal model of the environment.
-/

/-- Encode a history-percept observation as a binary prefix. -/
def perceptPrefix (h : History) (p : Percept) : BinString :=
  Mettapedia.UniversalAI.ValueUnderIgnorance.encodeHistory h ++
    Mettapedia.UniversalAI.ValueUnderIgnorance.encodePerceptBin p

/-- Prefix scores from the fixed complexity-weighted mixture. This does not
assert normalization as a conditional percept distribution. -/
noncomputable def modelEnvProb (U : PrefixFreeMachine) [OutputComplete U] : EnvProb :=
  fun h p => Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge.M₃ U
    (perceptPrefix h p)

/-! ## Part 2: Gödel Machine with Solomonoff Prior

A Gödel Machine that uses the Solomonoff prior for its environment model.
-/

/-- A Gödel Machine using Solomonoff prior for environment modeling. -/
structure SolomonoffGodelMachine (U : PrefixFreeMachine) [OutputComplete U] extends
    GodelMachineState where
  /-- Consistency: the envProb is derived from the Solomonoff model -/
  env_consistent : envProb = modelEnvProb U
  /-- Nonnegative tolerance in the fixed-model utility comparison. -/
  utilityTolerance : ℕ

/-- Install the fixed mixture model into an existing agent state, retaining
its policy, utility, interpreter and horizon. -/
noncomputable def SolomonoffGodelMachine.withModel
    (U : PrefixFreeMachine) [OutputComplete U]
    (state : GodelMachineState) (tolerance : Nat) : SolomonoffGodelMachine U where
  toGodelMachineState := { state with envProb := modelEnvProb U }
  env_consistent := rfl
  utilityTolerance := tolerance

/-! ## Part 3: Dominance Theorems

The Solomonoff prior dominates any computable environment model.
-/

/-- The universal prior dominates any computable environment. -/
theorem solomonoff_dominates_LSC {U : PrefixFreeMachine} [OutputComplete U]
    (μ : Mettapedia.UniversalAI.UniversalPrediction.PrefixMeasure)
    (hμ : Mettapedia.UniversalAI.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    ∃ c : ENNReal, c ≠ 0 ∧ ∀ x : BinString, c * μ x ≤ Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge.M₃ U x := by
  classical
  rcases
      (Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge.relEntropy_le_codeKpf_log2_M₃
        (U := U) (μ := μ) hμ 0) with ⟨code, hdom, _⟩
  let c : ENNReal := Mettapedia.UniversalAI.UniversalPrediction.HutterV3Kpf.codeWeight (U := U) code
  have hc0 : c ≠ 0 := by
    -- `kpfWeight` is a positive power of 2.
    unfold c Mettapedia.UniversalAI.UniversalPrediction.HutterV3Kpf.codeWeight
      Mettapedia.UniversalAI.UniversalPrediction.kpfWeight
    have hne0 : (2 : ENNReal) ≠ 0 := by norm_num
    have hneTop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    exact ne_of_gt (ENNReal.zpow_pos hne0 hneTop _)
  refine ⟨c, hc0, ?_⟩
  intro x
  simpa [c] using (hdom x)

/-- Corollary: Predictions under M are never too far from any computable model. -/
theorem prediction_dominance {U : PrefixFreeMachine} [OutputComplete U]
    (μ : Mettapedia.UniversalAI.UniversalPrediction.PrefixMeasure)
    (hμ : Mettapedia.UniversalAI.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ)
    (x : BinString) :
    ∃ c : ENNReal, c ≠ 0 ∧ Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge.M₃ U x ≥ c * μ x := by
  rcases solomonoff_dominates_LSC (U := U) (μ := μ) hμ with ⟨c, hc0, hdom⟩
  exact ⟨c, hc0, by simpa [mul_comm] using hdom x⟩

/-! ## Policy comparison under a fixed model -/

/-- Expected utility from the empty history with the Solomonoff-model data fixed
    and only the policy allowed to vary. -/
noncomputable def policyExpectedUtilityFromStart {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelMachine U) (π : SelfModPolicy) : ℝ :=
  vValueRealistic G.toGodelMachineState.toRealisticValueData π [] G.toGodelMachineState.horizon

/-- A policy is within tolerance `K` if it is within `K` of every alternative policy
    evaluated against the same Solomonoff-model data. -/
def PolicyWithinTolerance {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelMachine U) (K : ℕ) : Prop :=
  ∀ π' : SelfModPolicy,
    policyExpectedUtilityFromStart G G.toGodelMachineState.policy ≥
    policyExpectedUtilityFromStart G π' - K

/-- Exact policy optimality implies every nonnegative utility tolerance. -/
theorem policyWithinTolerance_of_qreOptimal {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelMachine U) (hrealistic : G.toGodelMachineState.isQreOptimal) :
    PolicyWithinTolerance G (G.utilityTolerance) := by
  intro π'
  have hstart : History.wellFormed ([] : History) := by
    simp [History.wellFormed]
  have hopt := hrealistic [] hstart (π' [])
  have hopt' :
      policyExpectedUtilityFromStart G G.toGodelMachineState.policy ≥
        policyExpectedUtilityFromStart G π' := by
    simpa [policyExpectedUtilityFromStart, expectedUtilityFromStart,
      expectedUtility, GodelMachineState.isQreOptimal, GodelMachineState.realisticData,
      GodelMachineState.toRealisticValueData, vValueRealistic] using hopt
  have hgap :
      policyExpectedUtilityFromStart G π' - G.utilityTolerance ≤
        policyExpectedUtilityFromStart G π' := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le (G.utilityTolerance))
  exact le_trans hgap hopt'

/-- Increasing the permitted utility gap preserves policy comparison. -/
theorem policyWithinTolerance_mono {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelMachine U) {small large : Nat}
    (bound : PolicyWithinTolerance G small) (le : small ≤ large) :
    PolicyWithinTolerance G large := by
  intro alternative
  exact (sub_le_sub_left (Nat.cast_le.mpr le) _).trans (bound alternative)

/-! ## Part 6: Connection to Proof-Based Modification

The inherited oracle compares the numeric expected utilities of the old and
new agent states. It does not require their model or utility data to agree.
-/

/-- A Solomonoff Gödel Machine with proof oracle. -/
structure SolomonoffGodelWithOracle (U : PrefixFreeMachine) [OutputComplete U] extends
    SolomonoffGodelMachine U where
  /-- The proof search oracle -/
  oracle : ProofSearchOracle

/-- Oracle soundness gives a strict improvement in state-relative expected
utility. The candidate state may carry different model and utility data. -/
theorem oracle_sound_for_solomonoff {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelWithOracle U) (G' : GodelMachineState)
    (t : ℕ) (hfound : G.oracle.findProvenMod G.toGodelMachineState t = some G') :
    expectedUtilityFromStart G' > expectedUtilityFromStart G.toGodelMachineState := by
  -- By soundness of the formal system
  have hvalid := G.oracle.sound G.toGodelMachineState t G' hfound
  exact valid_modification_improves G.toGodelMachineState G' hvalid

/-- The sound modification oracle preserves expected utility. -/
theorem globalSwitch_nondecreasing {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelWithOracle U) (t : ℕ) :
    let G' := globalSwitchWithOracle G.oracle G.toGodelMachineState t
    expectedUtilityFromStart G'.newState ≥ expectedUtilityFromStart G.toGodelMachineState := by
  exact globalSwitchWithOracle_nondecreasing G.oracle G.toGodelMachineState t

/-- Combine state-relative switch utility with the initial state's policy
comparison. This does not assert preservation of the model after switching. -/
theorem policyOptimality_and_switchUtility {U : PrefixFreeMachine} [OutputComplete U]
    (G : SolomonoffGodelWithOracle U)
    (hrealistic : G.toGodelMachineState.isQreOptimal) :
    -- The machine is safe: modifications only improve utility
    (∀ t, expectedUtilityFromStart (globalSwitchWithOracle G.oracle G.toGodelMachineState t).newState ≥
          expectedUtilityFromStart G.toGodelMachineState) ∧
    -- The policy comparison uses the supplied nonnegative tolerance.
    PolicyWithinTolerance G.toSolomonoffGodelMachine (G.toSolomonoffGodelMachine.utilityTolerance) := by
  constructor
  · intro t
    exact globalSwitch_nondecreasing G t
  · exact policyWithinTolerance_of_qreOptimal G.toSolomonoffGodelMachine hrealistic

end Mettapedia.UniversalAI.GodelMachine.SolomonoffBridge
