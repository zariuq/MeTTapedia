import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Belief
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FusionExpressivity

/-!
# Unified carrier algebra

This module isolates the exact-real algebra shared by a typed workspace content
plane, a weighted-evidence metadata plane, and a recurrent control plane.
It deliberately distinguishes local refinement laws from whole-decoder
equivalence:

* disabling evidence-to-content coupling recovers the scalar workspace write;
* zero old precision recovers that write only when fresh precision is positive;
* posterior evidence follows fade-then-fuse, while an episode innovation ledger
  accumulates only fresh packets;
* persistent evidence decays once and fuses innovations, never a posterior that
  already contains its prior;
* precision-biased read mass is an exact exponential reweighting, with a
  nonnegative squared bias parameter.

Concrete tensor layout, binary32 evaluation, and library-internal GRU arithmetic
remain separate conformance obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Set
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.PLN.Evidence
open scoped ENNReal

/-! ## Packed-state accounting -/

/-- Packed width for content, posterior evidence, episode innovations, slot
types, frontier addresses, recurrent control, and two scalar counters. -/
def packedStateWidth
    (slots contentWidth evidenceWidth controlWidth : ℕ) : ℕ :=
  slots * contentWidth + 4 * slots * evidenceWidth +
    2 * slots + controlWidth + 2

/-- Adding two innovation coordinates per evidence feature is the exact
difference from the posterior-only layout. -/
theorem packedStateWidth_eq_posteriorOnly_add_innovations
    (slots contentWidth evidenceWidth controlWidth : ℕ) :
    packedStateWidth slots contentWidth evidenceWidth controlWidth =
      (slots * contentWidth + 2 * slots * evidenceWidth +
        2 * slots + controlWidth + 2) +
      2 * slots * evidenceWidth := by
  unfold packedStateWidth
  ring

/-- Small positive fixture covering every packed-state component. -/
theorem packedStateWidth_fixture :
    packedStateWidth 3 4 2 3 = 47 := by
  norm_num [packedStateWidth]

/-! ## Collision-free typed prior indices -/

/-- Exact finite domain of persistent-prior keys: three roles, the root or one
registered parent operator, and five argument positions. -/
abbrev HoleType (operatorCount : ℕ) :=
  Fin 3 × (Fin (operatorCount + 1) × Fin 5)

/-- Mixed-radix equivalence used by the executable prior table. -/
def holeTypeIndex (operatorCount : ℕ) :
    HoleType operatorCount ≃ Fin (3 * ((operatorCount + 1) * 5)) :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) finProdFinEquiv).trans
    finProdFinEquiv

/-- The index has the source formula
`role * ((operatorCount + 1) * 5) + parent * 5 + argument`. -/
theorem holeTypeIndex_val
    (operatorCount : ℕ) (hole : HoleType operatorCount) :
    (holeTypeIndex operatorCount hole).val =
      hole.1.val * ((operatorCount + 1) * 5) +
        hole.2.1.val * 5 + hole.2.2.val := by
  simp [holeTypeIndex, finProdFinEquiv]
  ring

/-- Distinct valid type triples cannot collide in the persistent-prior table. -/
theorem holeTypeIndex_injective (operatorCount : ℕ) :
    Function.Injective
      (fun hole : HoleType operatorCount ↦
        (holeTypeIndex operatorCount hole).val) := by
  intro first second equalValues
  apply (holeTypeIndex operatorCount).injective
  exact Fin.ext equalValues

/-! ## Content refinement and strict separation -/

/-- Scalar source-faithful content write. When `useBayesGain` is false, the
evidence plane cannot affect this write. -/
noncomputable def contentStep
    (useBayesGain : Bool)
    (current proposal learnedGate oldPrecision freshPrecision : ℝ) : ℝ :=
  let gain :=
    if useBayesGain then
      learnedGate * precisionGain oldPrecision freshPrecision
    else
      learnedGate
  caromMix current proposal gain

/-- The disabled-coupling endpoint is exactly the scalar workspace write. -/
@[simp] theorem contentStep_withoutBayes_eq_workspace
    (current proposal learnedGate oldPrecision freshPrecision : ℝ) :
    contentStep false current proposal learnedGate
        oldPrecision freshPrecision =
      caromMix current proposal learnedGate := by
  simp [contentStep]

/-- With no retained evidence and a genuinely positive fresh packet, the Bayes
gain is exactly one. The positivity premise excludes the defined `0/0 = 0`
boundary. -/
theorem precisionGain_zeroOld_eq_one
    (freshPrecision : ℝ) (hfresh : 0 < freshPrecision) :
    precisionGain 0 freshPrecision = 1 := by
  simp [precisionGain, hfresh.ne']

/-- Both precisions zero is the honest no-information boundary. -/
@[simp] theorem precisionGain_zero_zero :
    precisionGain 0 0 = 0 := by
  norm_num [precisionGain]

/-- The coupled content write locally refines the workspace write when the old
precision is zero and fresh precision is positive. -/
theorem contentStep_zeroOld_eq_workspace
    (current proposal learnedGate freshPrecision : ℝ)
    (hfresh : 0 < freshPrecision) :
    contentStep true current proposal learnedGate 0 freshPrecision =
      caromMix current proposal learnedGate := by
  simp [contentStep, precisionGain_zeroOld_eq_one freshPrecision hfresh]

/-- Positive old and fresh precision makes the Bayes gain strictly interior. -/
theorem precisionGain_strictly_damps
    (oldPrecision freshPrecision : ℝ)
    (hold : 0 < oldPrecision) (hfresh : 0 < freshPrecision) :
    precisionGain oldPrecision freshPrecision ∈ Ioo (0 : ℝ) 1 :=
  precisionGain_mem_Ioo oldPrecision freshPrecision hold hfresh

/-- The coupled carrier is not the workspace endpoint in general. -/
theorem positivePrecision_contentStep_separates :
    contentStep true 0 1 1 1 1 ≠
      caromMix 0 1 1 := by
  norm_num [contentStep, precisionGain, caromMix]

/-! ## Posterior evidence and episode innovations -/

/-- Evidence metadata separates the current posterior from the fresh evidence
created during the current episode. -/
structure EvidenceLedger where
  posterior : WeightedEvidence
  innovation : WeightedEvidence

/-- One evidence-plane transition: posterior evidence fades then fuses, while
the innovation ledger adds the fresh packet without reintroducing the prior. -/
noncomputable def evidenceStep
    (retention : ℝ≥0∞) (state : EvidenceLedger)
    (fresh : WeightedEvidence) : EvidenceLedger where
  posterior := WeightedEvidence.fadeThenFuse retention state.posterior fresh
  innovation := state.innovation + fresh

/-- Sequential evidence updates for one episode. -/
noncomputable def evidenceRun
    (retention : ℝ≥0∞) :
    EvidenceLedger → List WeightedEvidence → EvidenceLedger
  | state, [] => state
  | state, fresh :: rest =>
      evidenceRun retention (evidenceStep retention state fresh) rest

@[simp] theorem evidenceStep_posterior
    (retention : ℝ≥0∞) (state : EvidenceLedger)
    (fresh : WeightedEvidence) :
    (evidenceStep retention state fresh).posterior =
      WeightedEvidence.fadeThenFuse retention state.posterior fresh := rfl

@[simp] theorem evidenceStep_innovation
    (retention : ℝ≥0∞) (state : EvidenceLedger)
    (fresh : WeightedEvidence) :
    (evidenceStep retention state fresh).innovation =
      state.innovation + fresh := rfl

/-- The episode innovation is exactly the sum of fresh packets, independently
of posterior fading. -/
theorem evidenceRun_innovation
    (retention : ℝ≥0∞) (state : EvidenceLedger)
    (freshPackets : List WeightedEvidence) :
    (evidenceRun retention state freshPackets).innovation =
      state.innovation + freshPackets.sum := by
  induction freshPackets generalizing state with
  | nil => simp [evidenceRun]
  | cons fresh rest ih =>
      rw [evidenceRun, ih]
      simp [evidenceStep, add_assoc]

/-- At an episode boundary the persistent prior fades once and receives only
the episode innovation. -/
noncomputable def absorbInnovation
    (retention : ℝ≥0∞) (prior : WeightedEvidence)
    (episode : EvidenceLedger) : WeightedEvidence :=
  WeightedEvidence.fadeThenFuse retention prior episode.innovation

/-- The persistence update is exactly the existing weighted-evidence carrier
step with the episode innovation as its fresh command. -/
theorem absorbInnovation_eq_weightedEvidenceCarrier
    (retention confidenceWeight : ℝ≥0∞)
    (prior : WeightedEvidence) (episode : EvidenceLedger) :
    absorbInnovation retention prior episode =
      Architecture.weightedEvidenceCarrier.step () confidenceWeight
        ⟨retention, episode.innovation⟩ prior := by
  rfl

/-- Persistence disabled means no mutation, independently of the candidate
episode state. -/
noncomputable def maybeAbsorbInnovation
    (enabled : Bool) (retention : ℝ≥0∞)
    (prior : WeightedEvidence) (episode : EvidenceLedger) : WeightedEvidence :=
  if enabled then absorbInnovation retention prior episode else prior

@[simp] theorem maybeAbsorbInnovation_false
    (retention : ℝ≥0∞) (prior : WeightedEvidence)
    (episode : EvidenceLedger) :
    maybeAbsorbInnovation false retention prior episode = prior := rfl

/-- Scalar fixture: decaying prior `2` by one half and adding innovation `1`
gives `2`; reabsorbing posterior `3` instead would give `4`. -/
theorem posterior_reabsorption_doubleCounts_fixture :
    (1 / 2 : ℝ) * 2 + 1 = 2 ∧
      (1 / 2 : ℝ) * 2 + (2 + 1) = 4 := by
  norm_num

/-! ## Precision-biased reads -/

/-- The implementation parameterizes read-bias strength by a square. -/
def readBeta (root : ℝ) : ℝ := root ^ 2

theorem readBeta_nonnegative (root : ℝ) :
    0 ≤ readBeta root := by
  exact sq_nonneg root

/-- Logit after precision reweighting. The expected runtime domain is
`0 ≤ precision`, hence `1 + precision > 0`. -/
noncomputable def precisionBiasedLogit
    (base root precision : ℝ) : ℝ :=
  base + readBeta root * Real.log (1 + precision)

/-- Exact mass identity underlying the biased softmax read. -/
theorem exp_precisionBiasedLogit
    (base root precision : ℝ) :
    Real.exp (precisionBiasedLogit base root precision) =
      Real.exp base *
        Real.exp (readBeta root * Real.log (1 + precision)) := by
  simp [precisionBiasedLogit, Real.exp_add]

/-- Zero root recovers the unmodified workspace logit exactly. -/
@[simp] theorem precisionBiasedLogit_zeroRoot
    (base precision : ℝ) :
    precisionBiasedLogit base 0 precision = base := by
  simp [precisionBiasedLogit, readBeta]

/-- For nonzero bias strength, increasing nonnegative precision strictly
increases the biased logit at fixed base score. -/
theorem precisionBiasedLogit_strictMono_precision
    (base root first second : ℝ)
    (hroot : root ≠ 0) (hfirst : 0 ≤ first) (horder : first < second) :
    precisionBiasedLogit base root first <
      precisionBiasedLogit base root second := by
  have hlog :
      Real.log (1 + first) < Real.log (1 + second) := by
    apply Real.log_lt_log
    · linarith
    · linarith
  have hbeta : 0 < readBeta root := by
    exact sq_pos_of_ne_zero hroot
  simpa [precisionBiasedLogit, add_comm] using
    (add_lt_add_left (mul_lt_mul_of_pos_left hlog hbeta) base)

/-- Positive read bias is observationally nontrivial. -/
theorem positivePrecisionBias_separates :
    precisionBiasedLogit 0 1 0 ≠
      precisionBiasedLogit 0 1 1 := by
  have h := precisionBiasedLogit_strictMono_precision
    0 1 0 1 (by norm_num) (by norm_num) (by norm_num)
  exact ne_of_lt h

/-! ## A genuine recurrent control component -/

/-- Minimal product state exposing distinct content, evidence, and control
planes. -/
structure ProductState (Content Evidence Control : Type*) where
  content : Content
  evidence : Evidence
  control : Control

/-- Update only the control plane through an explicit recurrent transition. -/
def advanceControl
    {Content Evidence Input Control : Type*}
    (transition : Input → Control → Control) (input : Input)
    (state : ProductState Content Evidence Control) :
    ProductState Content Evidence Control :=
  { state with control := transition input state.control }

@[simp] theorem advanceControl_content
    {Content Evidence Input Control : Type*}
    (transition : Input → Control → Control) (input : Input)
    (state : ProductState Content Evidence Control) :
    (advanceControl transition input state).content = state.content := rfl

@[simp] theorem advanceControl_evidence
    {Content Evidence Input Control : Type*}
    (transition : Input → Control → Control) (input : Input)
    (state : ProductState Content Evidence Control) :
    (advanceControl transition input state).evidence = state.evidence := rfl

/-- Equal content and evidence do not erase history carried by recurrent
control. -/
theorem recurrentControl_history_separates :
    (advanceControl (fun input hidden : ℤ ↦ input + 2 * hidden) 3
      ({ content := 7, evidence := 11, control := 0 } :
        ProductState ℤ ℤ ℤ)).control ≠
    (advanceControl (fun input hidden : ℤ ↦ input + 2 * hidden) 3
      ({ content := 7, evidence := 11, control := 1 } :
        ProductState ℤ ℤ ℤ)).control := by
  norm_num [advanceControl]

#print axioms packedStateWidth_eq_posteriorOnly_add_innovations
#print axioms holeTypeIndex_val
#print axioms holeTypeIndex_injective
#print axioms contentStep_withoutBayes_eq_workspace
#print axioms precisionGain_zeroOld_eq_one
#print axioms contentStep_zeroOld_eq_workspace
#print axioms precisionGain_strictly_damps
#print axioms positivePrecision_contentStep_separates
#print axioms evidenceRun_innovation
#print axioms absorbInnovation_eq_weightedEvidenceCarrier
#print axioms maybeAbsorbInnovation_false
#print axioms posterior_reabsorption_doubleCounts_fixture
#print axioms exp_precisionBiasedLogit
#print axioms precisionBiasedLogit_strictMono_precision
#print axioms positivePrecisionBias_separates
#print axioms recurrentControl_history_separates

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
