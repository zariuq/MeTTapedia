# Cognitive architecture framework

Mettapedia/CognitiveArchitecture formalizes MetaMo, OpenPsi, MicroPsi, and their mathematical bridges.
This module doesn't contain sorries across thirty-one files.

## Modules

### MetaMo

MetaMo is a six-file motivational Q-module framework.

- `MetaMo/Basic.lean`
  - MetaMo/Basic.lean defines Q-module structure with scalar multiplication

- `MetaMo/Appraisal.lean`
  - MetaMo/Appraisal.lean defines environmental stimulus appraisal functors

- `MetaMo/Decision.lean`
  - MetaMo/Decision.lean defines action selection functors

- `MetaMo/Commutativity.lean`
  - MetaMo/Commutativity.lean proves appraisal-decision commutativity

- `MetaMo/Dynamics.lean`
  - MetaMo/Dynamics.lean proves stability via Banach fixed-point arguments

- `MetaMo/Main.lean`
  - MetaMo/Main.lean aggregates the MetaMo module surface

### OpenPsi

OpenPsi is a five-file formalization of Dorner Psi with six demands and four modulators.

- `OpenPsi/Basic.lean`
  - OpenPsi/Basic.lean defines demands, modulators, and action-selection rules

- `OpenPsi/FuzzyLogic.lean`
  - OpenPsi/FuzzyLogic.lean defines fuzzy satisfaction computation

- `OpenPsi/ActionSelection.lean`
  - OpenPsi/ActionSelection.lean defines demand-driven action selection

- `OpenPsi/MetaMoInstance.lean`
  - OpenPsi/MetaMoInstance.lean defines OpenPsi as a QModule over ENNReal

### MicroPsi

MicroPsi is a three-file formalization with seven demands and PAD decomposition.

- `MicroPsi/Basic.lean`
  - MicroPsi/Basic.lean defines demands, PAD model, and utility action selection

- `MicroPsi/MetaMoInstance.lean`
  - MicroPsi/MetaMoInstance.lean defines MicroPsi as a QModule over ENNReal

### Bridges

Bridges is five files of cross-architecture comparison and limits.

- `Bridges/PLNMetaMoBridge.lean`
  - Bridges/PLNMetaMoBridge.lean connects PLN evidence quantales to MetaMo

- `Bridges/OpenPsiMicroPsiBridge.lean`
  - Bridges/OpenPsiMicroPsiBridge.lean compares OpenPsi and MicroPsi as MetaMo instances

- `Bridges/ModelExpressiveness.lean`
  - Bridges/ModelExpressiveness.lean analyzes expressiveness boundaries

- `Bridges/MissingValueSystems.lean`
  - Bridges/MissingValueSystems.lean proves value-system gaps outside consequentialism

### Values

Values is nine files extending beyond consequentialism.

- `Values/SchwartzValues.lean`
  - Values/SchwartzValues.lean defines Schwartz ten-value circumplex structure

- `Values/MoralFoundations.lean`
  - Values/MoralFoundations.lean defines Haidt six moral foundations

- `Values/DeontologicalLayer.lean`
  - Values/DeontologicalLayer.lean defines duty constraints above consequential utility

- `Values/RelationalValues.lean`
  - Values/RelationalValues.lean defines individual-dependent relational values

- `Values/TemporalValues.lean`
  - Values/TemporalValues.lean defines legacy and future-generation value structure

- `Values/MetaValues.lean`
  - Values/MetaValues.lean defines values about values including corrigibility

- `Values/FOETBridge.lean`
  - Values/FOETBridge.lean connects value formalization to FOET

## Key results

- OpenPsi and MicroPsi are MetaMo QModule instances.
- Appraisal-decision commutativity is proven when the quantale is commutative.
- Contractivity is a sufficient condition for unique motivational equilibrium.
- Gap analysis shows that both base architectures are fundamentally consequentialist.
