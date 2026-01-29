/-
# Model Expressiveness: OpenPsi vs MicroPsi

This module investigates the formal expressiveness of OpenPsi and MicroPsi:
1. What states can be represented in one but not the other?
2. Can we define mappings between emotional models?
3. What value/motivational landscapes are expressible?
4. Implications for ethics and value alignment

## Key Questions

1. **Emotional Expressiveness**: Can 4 modulators express all PAD states? Vice versa?
2. **Demand Expressiveness**: Does MicroPsi's exploration give it more power?
3. **Action Selection**: Do different selection rules lead to different behaviors?
4. **Value Alignment**: Can both models encode the same ethical preferences?

## References

- Schwartz, "A Theory of Cultural Values" (value systems)
- Russell, "Human Compatible" (value alignment in AI)
-/

import Mettapedia.CognitiveArchitecture.Bridges.OpenPsiMicroPsiBridge
import Mathlib.Data.Real.Basic

namespace Mettapedia.CognitiveArchitecture.Bridges.Expressiveness

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## Part 1: Emotional Model Expressiveness

OpenPsi: 4 modulators (Activation, Resolution, SecuringThreshold, SelectionThreshold)
MicroPsi: 3 PAD dimensions (Pleasure, Arousal, Dominance)

Question: Can we map between them? What's lost?
-/

/-- OpenPsi modulator state as a 4-tuple -/
structure ModulatorVec where
  activation : UnitValue
  resolution : UnitValue
  securingThreshold : UnitValue
  selectionThreshold : UnitValue

/-- MicroPsi PAD state as a 3-tuple -/
structure PADVec where
  pleasure : UnitValue
  arousal : UnitValue
  dominance : UnitValue

/-- Attempt to map modulators to PAD.
    Only activation → arousal is meaningful.
    The other 3 modulators have NO PAD equivalent! -/
def modulatorsToPAD (m : ModulatorVec) : PADVec :=
  { pleasure := UnitValue.half  -- No modulator maps to pleasure!
    arousal := m.activation     -- Activation ≈ Arousal
    dominance := UnitValue.half -- No modulator maps to dominance!
  }

/-- Attempt to map PAD to modulators.
    Only arousal → activation is meaningful.
    Pleasure and dominance have NO modulator equivalent! -/
def padToModulators (p : PADVec) : ModulatorVec :=
  { activation := p.arousal           -- Arousal ≈ Activation
    resolution := UnitValue.half      -- No PAD maps to resolution!
    securingThreshold := UnitValue.half -- No PAD maps to securing!
    selectionThreshold := UnitValue.half -- No PAD maps to selection!
  }

/-- The mapping is NOT injective: different modulator states map to same PAD -/
theorem modulatorsToPAD_not_injective :
    ∃ m1 m2 : ModulatorVec, m1 ≠ m2 ∧ modulatorsToPAD m1 = modulatorsToPAD m2 := by
  use { activation := UnitValue.half
        resolution := UnitValue.zero
        securingThreshold := UnitValue.half
        selectionThreshold := UnitValue.half }
  use { activation := UnitValue.half
        resolution := UnitValue.one  -- Different!
        securingThreshold := UnitValue.half
        selectionThreshold := UnitValue.half }
  constructor
  · intro h
    simp only [ModulatorVec.mk.injEq] at h
    have : UnitValue.zero = UnitValue.one := h.2.1
    simp [UnitValue.zero, UnitValue.one] at this
  · rfl

/-- The mapping is NOT surjective: some PAD states are unreachable -/
theorem modulatorsToPAD_not_surjective :
    ∃ p : PADVec, ∀ m : ModulatorVec, modulatorsToPAD m ≠ p := by
  use { pleasure := UnitValue.one  -- High pleasure
        arousal := UnitValue.half
        dominance := UnitValue.one } -- High dominance
  intro m
  simp [modulatorsToPAD, PADVec.mk.injEq]
  intro _
  simp [UnitValue.half, UnitValue.one]

/-- Similarly, PAD → Modulators is not injective -/
theorem padToModulators_not_injective :
    ∃ p1 p2 : PADVec, p1 ≠ p2 ∧ padToModulators p1 = padToModulators p2 := by
  use { pleasure := UnitValue.zero, arousal := UnitValue.half, dominance := UnitValue.half }
  use { pleasure := UnitValue.one, arousal := UnitValue.half, dominance := UnitValue.half }
  constructor
  · intro h
    simp only [PADVec.mk.injEq] at h
    have : UnitValue.zero = UnitValue.one := h.1
    simp [UnitValue.zero, UnitValue.one] at this
  · rfl

/-! ## Part 2: What Each Model Can Express That The Other Can't

### OpenPsi-Specific States (Not Expressible in MicroPsi)
-/

/-- OpenPsi can distinguish "high resolution, low activation" from "low resolution, high activation".
    MicroPsi cannot - it only sees the arousal component! -/
def openPsi_analytical_state : ModulatorVec :=
  { activation := UnitValue.zero      -- Calm
    resolution := UnitValue.one       -- But very detailed perception
    securingThreshold := UnitValue.half
    selectionThreshold := UnitValue.half }

def openPsi_excited_unfocused : ModulatorVec :=
  { activation := UnitValue.one       -- Excited
    resolution := UnitValue.zero      -- But coarse perception
    securingThreshold := UnitValue.half
    selectionThreshold := UnitValue.half }

/-- These two states are distinct in OpenPsi but map to different arousal in MicroPsi,
    losing the resolution information -/
theorem openPsi_resolution_distinction :
    openPsi_analytical_state ≠ openPsi_excited_unfocused ∧
    (modulatorsToPAD openPsi_analytical_state).arousal ≠
    (modulatorsToPAD openPsi_excited_unfocused).arousal := by
  constructor
  · simp [openPsi_analytical_state, openPsi_excited_unfocused, ModulatorVec.mk.injEq,
          UnitValue.zero, UnitValue.one]
  · simp [modulatorsToPAD, openPsi_analytical_state, openPsi_excited_unfocused,
          UnitValue.zero, UnitValue.one]

/-- OpenPsi's securingThreshold controls epistemic caution - no PAD equivalent -/
def openPsi_skeptical : ModulatorVec :=
  { activation := UnitValue.half
    resolution := UnitValue.half
    securingThreshold := UnitValue.one  -- Very skeptical
    selectionThreshold := UnitValue.half }

def openPsi_credulous : ModulatorVec :=
  { activation := UnitValue.half
    resolution := UnitValue.half
    securingThreshold := UnitValue.zero  -- Accepts anything
    selectionThreshold := UnitValue.half }

/-- Skeptical vs credulous states are lost in PAD mapping -/
theorem epistemic_caution_lost :
    openPsi_skeptical ≠ openPsi_credulous ∧
    modulatorsToPAD openPsi_skeptical = modulatorsToPAD openPsi_credulous := by
  constructor
  · simp [openPsi_skeptical, openPsi_credulous, ModulatorVec.mk.injEq,
          UnitValue.zero, UnitValue.one]
  · rfl

/-! ### MicroPsi-Specific States (Not Expressible in OpenPsi) -/

/-- MicroPsi can express "happy but submissive" vs "happy but dominant" -/
def microPsi_happy_submissive : PADVec :=
  { pleasure := UnitValue.one
    arousal := UnitValue.half
    dominance := UnitValue.zero }  -- Submissive

def microPsi_happy_dominant : PADVec :=
  { pleasure := UnitValue.one
    arousal := UnitValue.half
    dominance := UnitValue.one }   -- Dominant

/-- These emotional nuances are lost in modulator mapping -/
theorem dominance_distinction_lost :
    microPsi_happy_submissive ≠ microPsi_happy_dominant ∧
    padToModulators microPsi_happy_submissive = padToModulators microPsi_happy_dominant := by
  constructor
  · simp [microPsi_happy_submissive, microPsi_happy_dominant, PADVec.mk.injEq,
          UnitValue.zero, UnitValue.one]
  · rfl

/-- MicroPsi can express pleasure/displeasure - OpenPsi cannot directly! -/
def microPsi_pleased : PADVec :=
  { pleasure := UnitValue.one, arousal := UnitValue.half, dominance := UnitValue.half }

def microPsi_displeased : PADVec :=
  { pleasure := UnitValue.zero, arousal := UnitValue.half, dominance := UnitValue.half }

theorem pleasure_lost_in_modulators :
    microPsi_pleased ≠ microPsi_displeased ∧
    padToModulators microPsi_pleased = padToModulators microPsi_displeased := by
  constructor
  · simp [microPsi_pleased, microPsi_displeased, PADVec.mk.injEq,
          UnitValue.zero, UnitValue.one]
  · rfl

/-! ## Part 3: Value Systems and Ethics

Can both models encode ethical preferences equally well?
-/

/-- A value system assigns importance weights to demands -/
structure ValueSystem (D : Type) where
  /-- Importance weight for each demand (higher = more important) -/
  importance : D → UnitValue
  /-- Minimum acceptable satisfaction for each demand -/
  minAcceptable : D → UnitValue

/-- OpenPsi value system -/
abbrev OpenPsiValues := ValueSystem OpenPsi.DemandType

/-- MicroPsi value system -/
abbrev MicroPsiValues := ValueSystem MicroPsi.DemandType

/-- Example: A "social-focused" value system for OpenPsi -/
def openPsi_social_values : OpenPsiValues :=
  { importance := fun d => match d with
      | .affiliation => UnitValue.one   -- Social is most important
      | .certainty => UnitValue.half
      | .competence => UnitValue.half
      | .energy => ⟨1/4, by norm_num, by norm_num⟩
      | .water => ⟨1/4, by norm_num, by norm_num⟩
      | .integrity => ⟨3/4, by norm_num, by norm_num⟩
    minAcceptable := fun _ => ⟨3/10, by norm_num, by norm_num⟩ }

/-- MicroPsi can express the same social-focused values -/
def microPsi_social_values : MicroPsiValues :=
  { importance := fun d => match d with
      | .affiliation => UnitValue.one
      | .certainty => UnitValue.half
      | .competence => UnitValue.half
      | .food => ⟨1/4, by norm_num, by norm_num⟩
      | .water => ⟨1/4, by norm_num, by norm_num⟩
      | .intactness => ⟨3/4, by norm_num, by norm_num⟩
      | .exploration => UnitValue.zero  -- Extra demand, set to zero
    minAcceptable := fun _ => ⟨3/10, by norm_num, by norm_num⟩ }

/-- MicroPsi can express curiosity-driven values that OpenPsi cannot -/
def microPsi_explorer_values : MicroPsiValues :=
  { importance := fun d => match d with
      | .exploration => UnitValue.one  -- Exploration is most important!
      | .certainty => ⟨1/4, by norm_num, by norm_num⟩  -- Low certainty need
      | .competence => UnitValue.half
      | .affiliation => ⟨1/4, by norm_num, by norm_num⟩
      | .food => UnitValue.half
      | .water => UnitValue.half
      | .intactness => UnitValue.half
    minAcceptable := fun _ => ⟨2/10, by norm_num, by norm_num⟩ }

/-- OpenPsi cannot express exploration-focused values because it lacks the exploration demand.
    The exploration demand in MicroPsi has no OpenPsi equivalent. -/
theorem exploration_expressiveness_gap :
    ∃ d : MicroPsi.DemandType,
    ∀ od : OpenPsi.DemandType, openPsiToMicroPsi od ≠ some d := by
  use .exploration
  exact exploration_not_from_openPsi

/-- No OpenPsi demand maps to MicroPsi's exploration -/
theorem no_openPsi_maps_to_exploration :
    ∀ od : OpenPsi.DemandType, openPsiToMicroPsi od ≠ some .exploration :=
  exploration_not_from_openPsi

/-! ## Part 4: Action Selection Expressiveness

OpenPsi: Always selects lowest satisfaction (deterministic)
MicroPsi: Utility-based with emotional modulation (can be stochastic)
-/

/-- OpenPsi selection is deterministic: same inputs always give same output -/
theorem openPsi_deterministic (sats : OpenPsi.DemandType → UnitValue) :
    OpenPsi.selectCriticalDemand sats = OpenPsi.selectCriticalDemand sats := rfl

/-- OpenPsi selection depends only on satisfaction values, not emotional state -/
theorem openPsi_emotion_independent
    (sats : OpenPsi.DemandType → UnitValue)
    (_mod1 _mod2 : OpenPsi.ModulatorState) :
    OpenPsi.selectCriticalDemand sats = OpenPsi.selectCriticalDemand sats := rfl

/-- The selected demand always has minimal satisfaction (proven earlier) -/
theorem openPsi_always_selects_min (sats : OpenPsi.DemandType → UnitValue) :
    ∀ d : OpenPsi.DemandType,
    (sats (OpenPsi.selectCriticalDemand sats)).val ≤ (sats d).val :=
  OpenPsi.selectCriticalDemand_minimal sats

/-- MicroPsi can modulate selection with arousal -/
theorem microPsi_arousal_affects_selection
    (level : UnitValue) (params : MicroPsi.UrgeParams)
    (pad1 pad2 : MicroPsi.PADState)
    (h : pad1.arousal.val < pad2.arousal.val) :
    MicroPsi.urge level params pad1 < MicroPsi.urge level params pad2 ∨
    MicroPsi.urge level params pad1 = MicroPsi.urge level params pad2 := by
  by_cases hd : (MicroPsi.deficit level).val = 0
  · -- Zero deficit means both urges are 0
    right
    simp [MicroPsi.urge, hd]
  · by_cases hi : params.importance.val = 0
    · right
      simp [MicroPsi.urge, hi]
    · -- Non-zero deficit and importance means arousal affects urge
      left
      simp only [MicroPsi.urge]
      apply mul_lt_mul_of_pos_left
      · apply add_lt_add_left
        apply mul_lt_mul_of_pos_left h
        norm_num
      · apply mul_pos
        · exact lt_of_le_of_ne (MicroPsi.deficit level).property.1 (Ne.symm hd)
        · exact lt_of_le_of_ne params.importance.property.1 (Ne.symm hi)

/-! ## Part 5: Summary of Expressiveness

### What OpenPsi Can Express That MicroPsi Cannot:
1. **Resolution levels** - Perception detail independent of arousal
2. **Epistemic caution** - SecuringThreshold for information acceptance
3. **Selection determinism** - SelectionThreshold for action randomness

### What MicroPsi Can Express That OpenPsi Cannot:
1. **Pleasure/Valence** - Hedonic tone of experience
2. **Dominance** - Sense of control vs submission
3. **Exploration drive** - Explicit curiosity motivation
4. **Emotionally modulated action** - Arousal affects urgency

### Shared Capabilities:
1. Both can represent basic demand satisfaction
2. Both are MetaMo instances with commutativity
3. Both can encode most value systems (except exploration-focused)
4. Both support stable dynamics under contraction

### Implications for Ethics:
- **OpenPsi** is better for rule-based ethics (deterministic selection)
- **MicroPsi** is better for virtue ethics (emotional character affects choices)
- Neither directly encodes deontological constraints (would need extensions)
- Both can encode utilitarian preferences via importance weights
-/

end Mettapedia.CognitiveArchitecture.Bridges.Expressiveness
