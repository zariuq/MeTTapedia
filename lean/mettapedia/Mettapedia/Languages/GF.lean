/-
# Grammatical Framework (GF) Formalization in Lean

Full Czech morphology ported from GF Resource Grammar Library (ResCze.gf).

## Status (2026-02-13)

- **Infrastructure**: Core GF abstractions (Core, Abstract, Concrete)
- **Czech nouns**: 14 paradigms (PAN through STAVENI)
- **Czech adjectives**: 5 paradigms (hard/soft/possessive/invariable), 56-slot dispatch
- **Czech verbs**: copula + have + productive -ovat class, 6-person conjugation
- **Czech pronouns**: personal (8), possessive (7), reflexive, demonstrative, interrogative
- **Czech numerals**: 1-4 + 5+ + invariable, NumSize-governed agreement
- **Czech agreement**: NumSize form/agr dispatch (quantitative genitive for 5+)
- **0 sorries**: All proofs via `decide`, `simp`, or `rfl` (sound kernel reduction)
- **Known issues**: irregular stem alternations (pes→psa), epenthesis (okno→oken)

## Usage

```lean
import Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Czech.Declensions

def myNoun := declPAN "pán"
#eval declineFull myNoun ⟨Case.Gen, Number.Sg⟩  -- "pána"
```

## References

- GF Tutorial: http://www.grammaticalframework.org/
- GF-RGL Czech: ~/claude/gf-rgl/src/czech/
- Grammar compression: ~/claude/grammar_compression_FAIR.txt
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
import Mettapedia.Languages.GF.OSLFBridge
