/-
# Cognitive Architecture Bridges

This module collects bridges between different parts of the cognitive architecture
formalization and other Mettapedia modules.

## Contents

- `PLNMetaMoBridge.lean`: Connection between PLN evidence theory and MetaMo dynamics
- `OpenPsiMicroPsiBridge.lean`: Formal comparison of OpenPsi and MicroPsi architectures
- `ModelExpressiveness.lean`: What each model can express that the other cannot
- `MissingValueSystems.lean`: Value systems neither model can express (Schwartz, Haidt, etc.)
-/

import Mettapedia.CognitiveArchitecture.Bridges.PLNMetaMoBridge
import Mettapedia.CognitiveArchitecture.Bridges.OpenPsiMicroPsiBridge
import Mettapedia.CognitiveArchitecture.Bridges.ModelExpressiveness
import Mettapedia.CognitiveArchitecture.Bridges.MissingValueSystems
