import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ActiveSlotRestriction
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.StateCarrier

/-!
# Evidence-transition closure for the unified carrier

This module closes the evidence plane at both exact semantic levels used by
the carrier.  On the rational routed path, idle posterior fading can be jumped
by a power and commutes with slot restriction; nonnegative routed evidence is
preserved.  On the extended-nonnegative-real belief path, finite coordinates
are preserved by fade-then-fuse and by the complete evidence-ledger update.

The final section sends both a legal and an illegal operator through an actual
indexed carrier step before the shared checker-owned support mask is applied.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.PLN.Evidence
open scoped ENNReal

/-! ## Exact rational fade jumps -/

/-- Fade only the posterior evidence planes of a routed state.  Content and
episode innovations are unchanged during an idle evidence interval. -/
def rationalEvidenceFade
    {slots contentWidth evidenceWidth : ℕ} (retention : ℚ)
    (state : RoutedTensorState slots contentWidth evidenceWidth) :
    RoutedTensorState slots contentWidth evidenceWidth where
  content := state.content
  nPlus slot feature := retention * state.nPlus slot feature
  nMinus slot feature := retention * state.nMinus slot feature
  innovationPlus := state.innovationPlus
  innovationMinus := state.innovationMinus

/-- A routed packet with no content write and no fresh evidence. -/
def idleRoutedPacket
    {operators slots contentWidth evidenceWidth : ℕ} (retention : ℚ) :
    RoutedTensorPacket operators slots contentWidth evidenceWidth where
  precision := fun _ _ => 0
  freshPlus := fun _ _ => 0
  freshMinus := fun _ _ => 0
  retention := fun _ _ => retention
  candidate := fun _ _ => 0
  learnedGate := fun _ _ => 0

/-- The complete already-routed transition for an idle packet is exactly the
rational posterior fade. -/
theorem routedTensorStep_idle_state
    {operators slots contentWidth evidenceWidth : ℕ}
    (useBayesGain : Bool) (retention : ℚ)
    (state : RoutedTensorState slots contentWidth evidenceWidth) :
    (routedTensorStep useBayesGain state
      (idleRoutedPacket (operators := operators) retention)).state =
        rationalEvidenceFade retention state := by
  ext <;> simp [routedTensorStep, idleRoutedPacket, rationalEvidenceFade,
    finiteMean]

/-- `steps` idle fades equal one multiplication by the retention power. -/
theorem rationalEvidenceFade_iterate
    {slots contentWidth evidenceWidth : ℕ} (retention : ℚ)
    (state : RoutedTensorState slots contentWidth evidenceWidth)
    (steps : ℕ) :
    (rationalEvidenceFade retention)^[steps] state =
      rationalEvidenceFade (retention ^ steps) state := by
  induction steps with
  | zero =>
      ext <;> simp [rationalEvidenceFade]
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [rationalEvidenceFade, pow_succ]
      <;> ring

/-- Posterior fading commutes exactly with active-slot restriction. -/
theorem rationalEvidenceFade_reindexSlots
    {large small contentWidth evidenceWidth : ℕ}
    (route : Fin small → Fin large) (retention : ℚ)
    (state : RoutedTensorState large contentWidth evidenceWidth) :
    (rationalEvidenceFade retention state).reindexSlots route =
      rationalEvidenceFade retention (state.reindexSlots route) := by
  rfl

/-- Power-jumping a run of idle fades can therefore be performed directly on
the compact active-slot state. -/
theorem rationalEvidenceFade_iterate_reindexSlots
    {large small contentWidth evidenceWidth : ℕ}
    (route : Fin small → Fin large) (retention : ℚ)
    (state : RoutedTensorState large contentWidth evidenceWidth)
    (steps : ℕ) :
    ((rationalEvidenceFade retention)^[steps] state).reindexSlots route =
      rationalEvidenceFade (retention ^ steps) (state.reindexSlots route) := by
  rw [rationalEvidenceFade_iterate, rationalEvidenceFade_reindexSlots]

/-! ## Rational nonnegativity -/

/-- Every routed evidence-state coordinate is nonnegative. -/
structure RoutedTensorState.EvidenceNonnegative
    {slots contentWidth evidenceWidth : ℕ}
    (state : RoutedTensorState slots contentWidth evidenceWidth) : Prop where
  nPlus : ∀ slot feature, 0 ≤ state.nPlus slot feature
  nMinus : ∀ slot feature, 0 ≤ state.nMinus slot feature
  innovationPlus : ∀ slot feature, 0 ≤ state.innovationPlus slot feature
  innovationMinus : ∀ slot feature, 0 ≤ state.innovationMinus slot feature

/-- Every routed packet coordinate which enters evidence arithmetic is
nonnegative.  Precision is included because it also feeds the Bayes gain. -/
structure RoutedTensorPacket.EvidenceNonnegative
    {operators slots contentWidth evidenceWidth : ℕ}
    (packet : RoutedTensorPacket operators slots contentWidth evidenceWidth) :
    Prop where
  precision : ∀ slot feature, 0 ≤ packet.precision slot feature
  freshPlus : ∀ slot feature, 0 ≤ packet.freshPlus slot feature
  freshMinus : ∀ slot feature, 0 ≤ packet.freshMinus slot feature
  retention : ∀ slot feature, 0 ≤ packet.retention slot feature

/-- Fade-then-fuse and innovation addition preserve rational nonnegativity on
the actual routed transition. -/
theorem routedTensorStep_evidence_nonnegative
    {operators slots contentWidth evidenceWidth : ℕ}
    (useBayesGain : Bool)
    (state : RoutedTensorState slots contentWidth evidenceWidth)
    (packet : RoutedTensorPacket operators slots contentWidth evidenceWidth)
    (hstate : state.EvidenceNonnegative)
    (hpacket : packet.EvidenceNonnegative) :
    (routedTensorStep useBayesGain state packet).state.EvidenceNonnegative where
  nPlus slot feature :=
    add_nonneg (mul_nonneg (hpacket.retention slot feature)
      (hstate.nPlus slot feature)) (hpacket.freshPlus slot feature)
  nMinus slot feature :=
    add_nonneg (mul_nonneg (hpacket.retention slot feature)
      (hstate.nMinus slot feature)) (hpacket.freshMinus slot feature)
  innovationPlus slot feature :=
    add_nonneg (hstate.innovationPlus slot feature)
      (hpacket.freshPlus slot feature)
  innovationMinus slot feature :=
    add_nonneg (hstate.innovationMinus slot feature)
      (hpacket.freshMinus slot feature)

/-! ## Finite coordinates on the weighted-evidence path -/

/-- Neither extended-nonnegative-real evidence coordinate is infinite. -/
def weightedEvidenceHasFiniteCoordinates (evidence : WeightedEvidence) : Prop :=
  evidence.pos ≠ ⊤ ∧ evidence.neg ≠ ⊤

theorem zero_hasFiniteCoordinates :
    weightedEvidenceHasFiniteCoordinates (0 : WeightedEvidence) := by
  simp [weightedEvidenceHasFiniteCoordinates]

/-- Finite retention and finite inputs are closed under online fade-then-fuse. -/
theorem fadeThenFuse_hasFiniteCoordinates
    (retention : ℝ≥0∞) (old fresh : WeightedEvidence)
    (hretention : retention ≠ ⊤)
    (hold : weightedEvidenceHasFiniteCoordinates old)
    (hfresh : weightedEvidenceHasFiniteCoordinates fresh) :
    weightedEvidenceHasFiniteCoordinates
      (WeightedEvidence.fadeThenFuse retention old fresh) := by
  constructor
  · change retention * old.pos + fresh.pos ≠ ⊤
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hretention hold.1, hfresh.1⟩
  · change retention * old.neg + fresh.neg ≠ ⊤
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hretention hold.2, hfresh.2⟩

/-- Finite weighted evidence is closed under independent fusion. -/
theorem add_hasFiniteCoordinates
    (first second : WeightedEvidence)
    (hfirst : weightedEvidenceHasFiniteCoordinates first)
    (hsecond : weightedEvidenceHasFiniteCoordinates second) :
    weightedEvidenceHasFiniteCoordinates (first + second) := by
  constructor
  · change first.pos + second.pos ≠ ⊤
    exact ENNReal.add_ne_top.mpr ⟨hfirst.1, hsecond.1⟩
  · change first.neg + second.neg ≠ ⊤
    exact ENNReal.add_ne_top.mpr ⟨hfirst.2, hsecond.2⟩

/-- Both the posterior and current-episode innovation have finite evidence
coordinates. -/
def EvidenceLedger.HasFiniteCoordinates (state : EvidenceLedger) : Prop :=
  weightedEvidenceHasFiniteCoordinates state.posterior ∧
    weightedEvidenceHasFiniteCoordinates state.innovation

/-- The complete evidence-ledger update preserves finiteness. -/
theorem evidenceStep_hasFiniteCoordinates
    (retention : ℝ≥0∞) (state : EvidenceLedger)
    (fresh : WeightedEvidence)
    (hretention : retention ≠ ⊤)
    (hstate : state.HasFiniteCoordinates)
    (hfresh : weightedEvidenceHasFiniteCoordinates fresh) :
    (evidenceStep retention state fresh).HasFiniteCoordinates := by
  exact ⟨fadeThenFuse_hasFiniteCoordinates retention
      state.posterior fresh hretention hstate.1 hfresh,
    add_hasFiniteCoordinates state.innovation fresh
      hstate.2 hfresh⟩

/-- Named bridge from the unified evidence update to the sealed weighted
fade-then-fuse law. -/
theorem unifiedEvidenceUpdate_eq_fadeThenFuse
    (retention : ℝ≥0∞) (state : EvidenceLedger)
    (fresh : WeightedEvidence) :
    (evidenceStep retention state fresh).posterior =
      WeightedEvidence.fadeThenFuse retention state.posterior fresh := by
  rfl

/-! ## Exact positive and negative evidence examples -/

def oneSlotEvidenceState : RoutedTensorState 1 1 1 where
  content := fun _ _ => 7
  nPlus := fun _ _ => 4
  nMinus := fun _ _ => 8
  innovationPlus := fun _ _ => 3
  innovationMinus := fun _ _ => 5

def oneSlotActiveEvidencePacket : RoutedTensorPacket 1 1 1 1 where
  precision := fun _ _ => 1
  freshPlus := fun _ _ => 1
  freshMinus := fun _ _ => 0
  retention := fun _ _ => 1 / 2
  candidate := fun _ _ => 0
  learnedGate := fun _ _ => 0

/-- Two half-retention idle steps jump exactly to quarter retention. -/
theorem halfFade_twoStep_exact :
    ((rationalEvidenceFade (1 / 2))^[2] oneSlotEvidenceState).nPlus 0 0 = 1 ∧
      ((rationalEvidenceFade (1 / 2))^[2] oneSlotEvidenceState).nMinus 0 0 = 2 := by
  norm_num [rationalEvidenceFade_iterate, rationalEvidenceFade,
    oneSlotEvidenceState]

/-- An active fresh packet cannot be skipped as if the interval were idle. -/
theorem activeEvidenceRevision_ne_idleFade :
    (routedTensorStep false oneSlotEvidenceState
        oneSlotActiveEvidencePacket).state ≠
      rationalEvidenceFade (1 / 2) oneSlotEvidenceState := by
  intro heq
  have hpos := congrArg
    (fun state : RoutedTensorState 1 1 1 => state.nPlus 0 0) heq
  norm_num [routedTensorStep, rationalEvidenceFade, oneSlotEvidenceState,
    oneSlotActiveEvidencePacket] at hpos

theorem oneSlotEvidenceState_nonnegative :
    oneSlotEvidenceState.EvidenceNonnegative := by
  constructor <;> norm_num [oneSlotEvidenceState]

theorem oneSlotActiveEvidencePacket_nonnegative :
    oneSlotActiveEvidencePacket.EvidenceNonnegative := by
  constructor <;> norm_num [oneSlotActiveEvidencePacket]

/-- Negative retention is the exact missing premise: it sends positive
rational evidence below zero. -/
theorem negativeRetention_breaks_nonnegativity :
    let packet : RoutedTensorPacket 1 1 1 1 :=
      { oneSlotActiveEvidencePacket with
        retention := fun _ _ => -1
        freshPlus := fun _ _ => 0 }
    ¬ (routedTensorStep false oneSlotEvidenceState packet).state.EvidenceNonnegative := by
  dsimp only
  intro hnonnegative
  have hpos := hnonnegative.nPlus 0 0
  norm_num [routedTensorStep, oneSlotEvidenceState,
    oneSlotActiveEvidencePacket] at hpos

theorem finiteEvidenceUpdate_positiveExample :
    (evidenceStep (1 / 2)
      ⟨(⟨2, 3⟩ : WeightedEvidence), (⟨1, 1⟩ : WeightedEvidence)⟩
      (⟨4, 5⟩ : WeightedEvidence)).HasFiniteCoordinates := by
  apply evidenceStep_hasFiniteCoordinates
  · norm_num
  · constructor
    · constructor <;> norm_num
    · constructor <;> norm_num
  · constructor <;> norm_num

/-- Infinite prior evidence remains infinite under unit retention; finiteness
cannot be inferred without the finite-coordinate premises. -/
theorem infiniteEvidence_not_finite_after_update :
    ¬ (evidenceStep 1
      ⟨(⟨⊤, 0⟩ : WeightedEvidence), 0⟩
      (0 : WeightedEvidence)).HasFiniteCoordinates := by
  intro hfinite
  have hpos := hfinite.1.1
  change (1 * (⊤ : ℝ≥0∞) + 0) ≠ ⊤ at hpos
  simp at hpos

/-! ## Checker-owned support after an actual carrier step -/

noncomputable def supportExampleLedger : EvidenceLedger := ⟨0, 0⟩

noncomputable def supportExampleState : IndexedState Unit where
  content := fun _ => 0
  evidence := fun _ => supportExampleLedger
  control := 0

noncomputable def supportExampleCommand : IndexedCommand Unit where
  contentProposal := fun _ => 1
  learnedGate := fun _ => 1
  routedOldPrecision := fun _ => 1
  routedFreshPrecision := fun _ => 1
  retention := fun _ => 1
  freshEvidence := fun _ => 0
  controlInput := 1

def supportExampleMode : IndexedMode Unit where
  useBayesGain := true
  readSlot := ()
  controlRetention := 1
  evidencePolicyWeight := 0
  controlPolicyWeight := 1

def supportExampleDecision (state : IndexedState Unit) : ℝ :=
  state.content () + state.control

/-- A legal operator remains present after the complete product carrier has
updated all three state planes. -/
theorem legalOperator_present_after_carrierStep :
    (sourcePolicyReadout
      (fun _ : Unit => true)
      (fun decision : ℝ => fun _ : Unit => decision)
      (fun _ : Unit => (1 : ℝ))
      (fun decision context : ℝ => decision + context)
      (fun readout embedding : ℝ => readout * embedding)
      (fun operator : Bool => if operator then (2 : ℝ) else 1)
      (fun _ : Bool => (0 : ℝ))
      (fun operator : Bool => !operator)
      (supportExampleDecision
        (indexedUnifiedCarrier.step supportExampleState supportExampleMode
          supportExampleCommand supportExampleState))
      false).isSome = true := by
  exact sourcePolicyAfterUnifiedStep_isSome supportExampleState
    supportExampleState supportExampleMode supportExampleCommand
    supportExampleDecision (fun _ : Unit => true)
    (fun decision : ℝ => fun _ : Unit => decision)
    (fun _ : Unit => (1 : ℝ))
    (fun decision context : ℝ => decision + context)
    (fun readout embedding : ℝ => readout * embedding)
    (fun operator : Bool => if operator then (2 : ℝ) else 1)
    (fun _ : Bool => (0 : ℝ)) (fun operator : Bool => !operator) false

/-- No state produced by the actual carrier step can make the illegal Boolean
operator appear in the shared policy readout. -/
theorem illegalOperator_absent_after_carrierStep :
    sourcePolicyReadout
      (fun _ : Unit => true)
      (fun decision : ℝ => fun _ : Unit => decision)
      (fun _ : Unit => (1 : ℝ))
      (fun decision context : ℝ => decision + context)
      (fun readout embedding : ℝ => readout * embedding)
      (fun operator : Bool => if operator then (2 : ℝ) else 1)
      (fun _ : Bool => (0 : ℝ))
      (fun operator : Bool => !operator)
      (supportExampleDecision
        (indexedUnifiedCarrier.step supportExampleState supportExampleMode
          supportExampleCommand supportExampleState))
      true = none := by
  simp [sourcePolicyReadout, legalMaskedScore]

#print axioms rationalEvidenceFade_iterate
#print axioms rationalEvidenceFade_iterate_reindexSlots
#print axioms routedTensorStep_evidence_nonnegative
#print axioms evidenceStep_hasFiniteCoordinates
#print axioms unifiedEvidenceUpdate_eq_fadeThenFuse
#print axioms activeEvidenceRevision_ne_idleFade
#print axioms negativeRetention_breaks_nonnegativity
#print axioms infiniteEvidence_not_finite_after_update
#print axioms legalOperator_present_after_carrierStep
#print axioms illegalOperator_absent_after_carrierStep

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
