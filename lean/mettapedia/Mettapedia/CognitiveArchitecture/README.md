# Mettapedia/CognitiveArchitecture

Formalization of cognitive architecture frameworks: MetaMo (motivational meta-model),
OpenPsi (Dorner's Psi theory), MicroPsi (Bach), and their mathematical connections.

31 files, zero sorries.

## Modules

### MetaMo/ (6 files)
Core mathematical framework from Goertzel & Lian, "Weakness and Its Quantale."
Motivational states as Q-modules over commutative quantales.

- `Basic.lean` — Q-module structure with scalar multiplication
- `Appraisal.lean` — Environmental stimulus evaluation functor
- `Decision.lean` — Action selection functor
- `Commutativity.lean` — Appraisal-decision commutativity (central theorem)
- `Dynamics.lean` — Stability via Banach fixed-point theorem
- `Main.lean` — Module aggregation

### OpenPsi/ (5 files)
Correct formalization of Dorner's Psi theory (per OpenCog 2010). 6 demands
(Energy, Water, Integrity, Affiliation, Certainty, Competence), 4 modulators.
Corrects prior confusion between OpenPsi and PAD emotional model.

- `Basic.lean` — Demands, modulators, action selection rule
- `FuzzyLogic.lean` — Fuzzy satisfaction computation
- `ActionSelection.lean` — Demand-driven action selection
- `MetaMoInstance.lean` — OpenPsi as QModule over ENNReal (10-dim state vector)

### MicroPsi/ (3 files)
Joscha Bach's cognitive architecture. 7 demands, PAD emotional model
(Pleasure, Arousal, Dominance). Same 10-dimensional state space as OpenPsi
but different decomposition (3 PAD + 7 demands vs. 4 modulators + 6 demands).

- `Basic.lean` — Demands, PAD model, utility-based action selection
- `MetaMoInstance.lean` — MicroPsi as QModule over ENNReal

### Bridges/ (5 files)
Cross-architecture connections and analysis.

- `PLNMetaMoBridge.lean` — PLN evidence theory to MetaMo (both use commutative quantales)
- `OpenPsiMicroPsiBridge.lean` — Formal comparison: both are MetaMo instances, same dimension, different decomposition
- `ModelExpressiveness.lean` — Expressiveness analysis
- `MissingValueSystems.lean` — Value systems neither model can express (both fundamentally consequentialist)

### Values/ (9 files)
Unified value system extending OpenPsi/MicroPsi with non-consequentialist frameworks.

- `SchwartzValues.lean` — Schwartz's 10 universal values (circumplex structure)
- `MoralFoundations.lean` — Haidt's 6 moral foundations
- `DeontologicalLayer.lean` — Duty-based constraints overriding consequentialism
- `RelationalValues.lean` — Individual-dependent values (trust, loyalty, love)
- `TemporalValues.lean` — Legacy, future generations, sustainability
- `MetaValues.lean` — Values about values (learning, uncertainty, corrigibility)
- `FOETBridge.lean` — Bridge to Foundations of Ethics

## Key Results

- OpenPsi and MicroPsi are both MetaMo QModule instances (`both_are_qmodules`)
- Appraisal-decision commutativity when Q is commutative
- Contractivity implies unique motivational equilibrium (Banach fixed-point)
- Both architectures are fundamentally consequentialist (formal gap analysis)
