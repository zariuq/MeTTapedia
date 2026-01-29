/-
# OpenPsi Main Module (Corrected)

Imports all OpenPsi components based on actual sources:
- OpenCog Wiki OpenPsi (2010)
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (AGI 2011)
- Dörner's Psi theory foundations

## Contents

- `FuzzyLogic.lean`: Fuzzy satisfaction computation (fuzzy_within)
- `Basic.lean`: Correct demand types (Dörner), modulator state (NOT PAD!), demand state
- `ActionSelection.lean`: Lowest-satisfaction action selection rule
- `MetaMoInstance.lean`: OpenPsi as a QModule over ℝ≥0∞ (MetaMo instance)

## Key Corrections from Previous Implementation

| Component | Previous (WRONG) | Corrected |
|-----------|-----------------|-----------|
| Demands | energy, social, novelty, competence, safety, autonomy | Energy, Water, Integrity, Affiliation, Certainty, Competence |
| Modulators | PAD (valence, arousal, dominance) | Activation, Resolution, SecuringThreshold, SelectionThreshold |
| Satisfaction | deficit × decayRate × baseWeight | fuzzy_within(level, min, max) |
| Selection | Utility-based | Lowest satisfaction wins |

The PAD model is used by MicroPsi, NOT OpenPsi!
-/

import Mettapedia.CognitiveArchitecture.OpenPsi.FuzzyLogic
import Mettapedia.CognitiveArchitecture.OpenPsi.Basic
import Mettapedia.CognitiveArchitecture.OpenPsi.ActionSelection
import Mettapedia.CognitiveArchitecture.OpenPsi.MetaMoInstance
