# Languages

Mettapedia/Languages formalizes formal linguistics, natural language semantics, and process calculi.

## Modules

### GF formalization

GF formalizes a Lean 4 GF RGL subset with 170 abstract signatures, two concrete grammars, and a verified semantic bridge.
The Czech grammar includes 14 declension paradigms, verb conjugation, adjectives, pronouns, and numerals.
The English grammar includes full clause construction with tense, aspect, polarity, do-support, and relative clauses.

- The semantic bridge is GF -> Pattern -> Store -> QFormula -> Evidence -> NTT.
- The GF module doesn't contain sorries or axioms.
- GF/README.md contains the full architecture and file map.

#### GF SUMO pipeline

GF/SUMO runs top-down SUMO ontology repair through the GF-OSLF-WM pipeline.
The SUMO repair lane compares SUMO KIF, Enache's SUMO-GF encoding, and the flattened Lean encoding.
The full SUMO pipeline is SUMO KIF -> GF Pattern -> GSLT -> OSLF -> WM checkLang.
The class hierarchy is a rewrite system with proven Galois connection and NTT extraction.

- The SUMO lane uses six automated repair patterns.

#### SUMO file map

- `SumoAbstract.lean`
  - SumoAbstract.lean contains FOET-relevant classes, function signatures, and transitive closure

- `SumoOSLFBridge.lean`
  - SumoOSLFBridge.lean contains pipeline bridge and proven Galois connection with diagnostics

- `SumoNTT.lean`
  - SumoNTT.lean contains GSLT hierarchy, NTT extraction, and WM checkLang evaluation

- `SumoRepairRunner.lean`
  - SumoRepairRunner.lean performs three-source diffs with disagreement flags

- `SumoAxiomCensus.lean`
  - SumoAxiomCensus.lean provides per-concept usage evidence

- `RepairLog.lean`
  - RepairLog.lean tracks repair decisions and strengthening proposals

- `original/`
  - original/ is a read-only Enache and Angelov SUMO-GF reference

#### SUMO current status

- Layer 1 is complete with strata 0 and 1 coverage.
- The current log is 20 repair decisions with 19 automatable.
- FOET KIF is 12 applied fixes across syntax, argument swaps, and typing.
- checkLang proves that contraryAttribute Pleasure Pain is ill-typed.
- The class census is 53 analyzed classes with agreement, missing, flattened, and FOET-only buckets.
- Relation typing is three issues found and one fixed.
- Transitive closure is 54 direct edges with full closure diagnostics.
- Pain-Attribute conflict is automatically detected through coercion-path analysis.
- All SUMO files are clean with zero sorries.

### Process calculi formalization

ProcessCalculi formalizes pi-calculus and rho-calculus with operational semantics, structural congruence, and OSLF instances.
The process calculi lane includes Lybech pi-to-rho forward simulation and Meredith spice calculus.

- The pi-calculus module is 16 files for the asynchronous choice-free fragment.
- The rho-calculus module is 11 files with locally nameless COMM reduction and spice rule.
- The ProcessCalculi module doesn't contain sorries.
- ProcessCalculi/README.md contains detailed architecture and proof status.
