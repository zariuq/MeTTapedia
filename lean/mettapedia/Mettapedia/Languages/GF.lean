/-
# Grammatical Framework (GF) Formalization in Lean

Full Czech and English morphology ported from GF Resource Grammar Library.

## Status (2026-02-13)

- **Infrastructure**: Core GF abstractions (Core, Abstract, Concrete)
- **Abstract syntax**: 985 functions, 112 categories (full GF RGL)
- **Czech**: 14 noun paradigms, 5 adj paradigms, verbs, pronouns, numerals, agreement
- **English**: noun paradigms (regular + irregular), verb conjugation (regular + irregular +
  auxiliaries), adjective comparison, sentence construction (tense, aspect, polarity,
  do-support, word order), pronouns, prepositions, conjunctions
- **OSLF bridge**: GF grammars automatically get types via the OSLF pipeline
- **0 sorries**: All proofs via `decide`, `simp`, or `rfl` (sound kernel reduction)

## Usage

```lean
import Mettapedia.Languages.GF
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs

-- "the cat walks"
#eval! linUseCl .Pres .Simul .CPos
  (linPredVP (linDetCN theDefArt (linUseN cat_N)) (predV walk_V))
```

## References

- GF Tutorial: http://www.grammaticalframework.org/
- GF-RGL: ~/claude/gf-rgl/
-/

import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.Concrete
import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Czech.Declensions
import Mettapedia.Languages.GF.Czech.Adjectives
import Mettapedia.Languages.GF.Czech.Verbs
import Mettapedia.Languages.GF.Czech.Pronouns
import Mettapedia.Languages.GF.Czech.Numerals
import Mettapedia.Languages.GF.Czech.Agreement
import Mettapedia.Languages.GF.Czech.Examples
import Mettapedia.Languages.GF.Czech.Properties
import Mettapedia.Languages.GF.Czech.Tests
import Mettapedia.Languages.GF.Czech.Linearization
import Mettapedia.Languages.GF.English.Morphology
import Mettapedia.Languages.GF.English.Nouns
import Mettapedia.Languages.GF.English.Verbs
import Mettapedia.Languages.GF.English.Adjectives
import Mettapedia.Languages.GF.English.Syntax
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.Languages.GF.English.Relatives
import Mettapedia.Languages.GF.English.Properties
import Mettapedia.Languages.GF.English.Linearization
import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.RoundTripCorpus
import Mettapedia.Languages.GF.Czech.RoundTripCorpus
import Mettapedia.Languages.GF.RoundTripRegression
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.Typing
import Mettapedia.Languages.GF.LinguisticInvariance
import Mettapedia.Languages.GF.KernelConfluence
import Mettapedia.Languages.GF.SemanticKernelConfluence
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.Languages.GF.StoreToLogicalForm
import Mettapedia.Languages.GF.OSLFToNTT
import Mettapedia.Languages.GF.Examples.EveryManWalks
import Mettapedia.Languages.GF.Examples.ScopeAmbiguity
import Mettapedia.Languages.GF.Examples.AnaphoraBinding
