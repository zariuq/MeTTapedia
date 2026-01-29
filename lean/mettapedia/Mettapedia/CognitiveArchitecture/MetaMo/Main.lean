/-
# MetaMo: Motivational Meta-Model

This module provides a comprehensive formalization of the MetaMo (Motivational Meta-Model)
framework from Goertzel & Lian's work on quantale-based plausibility theory.

## Overview

MetaMo is a mathematical framework for AGI motivational dynamics based on:
1. **Q-modules**: Motivational state spaces over commutative quantales
2. **Appraisal functors**: Environmental sensitivity transformations
3. **Decision functors**: Goal-driven action selection transformations
4. **Contractive dynamics**: Stability guarantees via Banach fixed-point theorem

## Key Results

- `QModule`: The fundamental structure for motivational state spaces
- `appraisalFunctor`: The environmental appraisal transformation
- `decisionFunctor`: The goal-driven decision transformation
- `appraisal_decision_commute`: **Core theorem** - appraisal and decision commute
- `motivational_equilibrium_exists`: Under contractivity, a unique stable equilibrium exists

## File Structure

- `Basic.lean`: Q-module definition and basic properties
- `Appraisal.lean`: Appraisal functor and its properties
- `Decision.lean`: Decision functor and its properties
- `Commutativity.lean`: Main commutativity theorem
- `Dynamics.lean`: Contractive dynamics and stability

## References

- Goertzel & Lian, "Weakness and Its Quantale: Plausibility Theory from First Principles"
- Banach, "Sur les opérations dans les ensembles abstraits" (1922)
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Basic
import Mettapedia.CognitiveArchitecture.MetaMo.Appraisal
import Mettapedia.CognitiveArchitecture.MetaMo.Decision
import Mettapedia.CognitiveArchitecture.MetaMo.Commutativity
import Mettapedia.CognitiveArchitecture.MetaMo.Dynamics
