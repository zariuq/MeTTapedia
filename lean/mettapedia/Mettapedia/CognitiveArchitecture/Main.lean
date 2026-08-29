/-
# Cognitive Architecture Formalization

This module provides formal mathematical frameworks for AGI cognitive architectures,
specifically MetaMo (Motivational Meta-Model), OpenPsi, and MicroPsi.

## Modules

### MetaMo
A general mathematical framework for motivational dynamics based on Q-modules
over commutative quantales. Key results include:
- Commutativity of appraisal and decision functors
- Stability via Banach fixed-point theorem

### OpenPsi (Corrected)
A concrete instantiation of MetaMo based on Dörner's Psi theory with:
- **6 Demands** (Energy, Water, Integrity, Affiliation, Certainty, Competence)
- **4 Modulators** (Activation, Resolution, SecuringThreshold, SelectionThreshold)
- Fuzzy satisfaction computation
- Lowest-satisfaction action selection
- **QModule instance over ℝ≥0∞**

### MicroPsi
Joscha Bach's cognitive architecture with:
- **7 Demands** (Food, Water, Intactness, Affiliation, Certainty, Competence, Exploration)
- **PAD Emotional Model** (Pleasure, Arousal, Dominance)
- Utility-based action selection with emotional modulation
- **QModule instance over ℝ≥0∞**

### Bridges
Connections between modules:
- **PLN-MetaMo Bridge**: PLN truth values parameterize MetaMo dynamics
- **OpenPsi-MicroPsi Bridge**: Formal comparison of the two architectures
- **Model Expressiveness**: What each model can express that the other cannot
- **Missing Value Systems**: Value systems neither model can express

### Values (NEW)
Unified value system extending OpenPsi/MicroPsi to handle full scope of human values:
- **Schwartz's 10 Basic Values** with circular structure
- **Haidt's 6 Moral Foundations** with profile variations
- **Deontological Constraints** (forbidden/required actions)
- **Relational Values** (trust, loyalty, love for specific individuals)
- **Temporal Values** (legacy, future generations, sustainability)
- **Meta-Values** (value learning, moral uncertainty, corrigibility)

## Key Difference: OpenPsi vs MicroPsi

| Aspect | OpenPsi | MicroPsi |
|--------|---------|----------|
| Emotional Model | 4 Modulators | PAD (3 dimensions) |
| Demands | 6 | 7 (adds Exploration) |
| Action Selection | Lowest satisfaction | Utility-based |

## References

- Goertzel & Lian, "Weakness and Its Quantale: Plausibility Theory from First Principles"
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (AGI 2011)
- Bach, "MicroPsi 2: Modeling Motivation" (AGI 2015)
- Goertzel et al., "Probabilistic Logic Networks"
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.CognitiveArchitecture.Agent
import Mettapedia.CognitiveArchitecture.Agent.Bridges.PLN
import Mettapedia.CognitiveArchitecture.AttentionEconomy
import Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
import Mettapedia.CognitiveArchitecture.CognitiveSchematic
import Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy
import Mettapedia.CognitiveArchitecture.CognitiveSynergy
import Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
import Mettapedia.CognitiveArchitecture.CognitiveSynergyWave
import Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling
import Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
import Mettapedia.CognitiveArchitecture.TriggeredSpaceActivationPolicy
import Mettapedia.CognitiveArchitecture.MindAgentStoreAdmission
import Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
import Mettapedia.CognitiveArchitecture.FundedScheduledPremiseService
import Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService
import Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
import Mettapedia.CognitiveArchitecture.ForegroundChainingClosureBoundary
import Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
import Mettapedia.CognitiveArchitecture.AtomicForegroundBackgroundWave
import Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave
import Mettapedia.CognitiveArchitecture.ApproximateProtectedTransitionAdvice
import Mettapedia.CognitiveArchitecture.ProtectedForegroundBackgroundNIKArticle
import Mettapedia.CognitiveArchitecture.ForegroundBackgroundSemanticRouteBinding
import Mettapedia.CognitiveArchitecture.ForegroundBackgroundGSLTILRouteBridge
import Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
import Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
import Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
import Mettapedia.CognitiveArchitecture.AtomicRecurrentMindAgentWave
import Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentBackpressure
import Mettapedia.CognitiveArchitecture.FairRecurrentMindAgentBackpressure
import Mettapedia.CognitiveArchitecture.FiniteRecurrentPremiseCost
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentGSLTILRouteBridge
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentStreamProductivity
import Mettapedia.CognitiveArchitecture.NestedMindAgentExecutionBoundary
import Mettapedia.CognitiveArchitecture.MindWorldRepresentationRealization
import Mettapedia.CognitiveArchitecture.Agent.RevisionLineage
import Mettapedia.CognitiveArchitecture.Agent.ProtectedSelfRevision
import Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing
import Mettapedia.CognitiveArchitecture.EGIClaimTracker
import Mettapedia.CognitiveArchitecture.ProblemSolvingMethods
import Mettapedia.CognitiveArchitecture.OpenPsi.Main
import Mettapedia.CognitiveArchitecture.MicroPsi.Main
import Mettapedia.CognitiveArchitecture.Bridges.Main
import Mettapedia.CognitiveArchitecture.Values.Main
import Mettapedia.NARS.Bridges.CognitiveArchitecture
