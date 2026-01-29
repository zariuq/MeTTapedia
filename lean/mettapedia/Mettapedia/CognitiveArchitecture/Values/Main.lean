/-
# Unified Value System

This module provides a comprehensive formalization of human values that extends
OpenPsi and MicroPsi cognitive architectures beyond their consequentialist limitations.

## Modules

### Basic (`Basic.lean`)
Core value type definitions spanning multiple frameworks:
- Schwartz's 10 basic values
- Haidt's 6 moral foundations
- Meta-values (value learning, moral uncertainty, corrigibility)

### SchwartzValues (`SchwartzValues.lean`)
Schwartz's Theory of Basic Human Values:
- 10 universal values with circular structure
- Compatible and conflicting value pairs
- Higher-order value dimensions

### MoralFoundations (`MoralFoundations.lean`)
Haidt's Moral Foundations Theory:
- 6 innate moral foundations
- Political orientation profiles
- Foundation-trigger mappings

### DeontologicalLayer (`DeontologicalLayer.lean`)
Deontological constraints (duty-based ethics):
- Forbidden and required actions
- Promise-keeping obligations
- Truth-telling constraints

### RelationalValues (`RelationalValues.lean`)
Relational values (care ethics):
- Trust, loyalty, gratitude, forgiveness, love, friendship
- Energy-limited relationship maintenance
- Trust dynamics over time

### TemporalValues (`TemporalValues.lean`)
Temporal values:
- Legacy concerns
- Future generations welfare
- Sustainability
- Temporal discounting

### MetaValues (`MetaValues.lean`)
Meta-values (values about values):
- Value learning mechanisms
- Moral uncertainty reasoning
- Value pluralism
- Corrigibility

### FOETBridge (`FOETBridge.lean`)
Bridge to FOET (Foundations of Ethics) ontology:
- Extended moral attributes (FOET 3 + Haidt 6 × 2 polarities)
- FOET-style theory/semantics/entailment machinery
- Deontic ↔ Value bidirectional translation
- SUMO-compatible value signature
- Coverage and completeness theorems

## Key Findings

### OpenPsi/MicroPsi Gaps
- Neither covers ANY of Haidt's 6 moral foundations
- Both cover < 50% of Schwartz's 10 values
- Neither has deontological constraints (purely consequentialist)
- Neither has relational values (affiliation is scalar, not relational)
- Neither has temporal values (present-focused only)
- Neither has meta-values (no value learning)

### This Extension Provides
- All 10 Schwartz values
- All 6 moral foundations
- Deontological constraint layer
- Energy-limited relational values
- Temporal discounting and legacy
- Value learning with moral uncertainty

## References

- Schwartz, "A Theory of Cultural Values" (1992)
- Haidt, "The Righteous Mind" (2012)
- Russell, "Human Compatible" (2019)
- Gilligan, "In a Different Voice" (1982)
- Kant, "Groundwork of the Metaphysics of Morals" (1785)
-/

import Mettapedia.CognitiveArchitecture.Values.Basic
import Mettapedia.CognitiveArchitecture.Values.SchwartzValues
import Mettapedia.CognitiveArchitecture.Values.MoralFoundations
import Mettapedia.CognitiveArchitecture.Values.DeontologicalLayer
import Mettapedia.CognitiveArchitecture.Values.RelationalValues
import Mettapedia.CognitiveArchitecture.Values.TemporalValues
import Mettapedia.CognitiveArchitecture.Values.MetaValues
import Mettapedia.CognitiveArchitecture.Values.FOETBridge
