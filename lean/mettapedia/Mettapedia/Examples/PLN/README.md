# PLN examples and curriculum

This directory collects worked PLN and WM-PLN examples.  The curriculum files
are ordered so each one imports the live rule or bridge theorem it demonstrates,
then gives both a positive instance and a negative or boundary instance.

## Curriculum order

1. `RavenInductionCurriculum`
   - Uses the first-order raven induction bridge for forward and inverse
     evidence aggregation.
   - Keeps `ClassicExamples` as the older provenance entry that this wrapper
     supersedes for curriculum use.
2. `DiseaseAbductionCurriculum`
   - Uses the algorithmic abduction bridge for prior-sensitive hypothesis
     ranking.
   - Shows the base-rate trap and overlapping intervals as negative cases.
3. `BotnickMultiAgentEvidence`
   - Uses the multipath dependency module for disjoint sources, shared
     sublemmas, and duplicate-source redundancy.
   - Shows that revision can fall below the redundancy floor when dependence is
     ignored.
4. `EstimatorEnvelopeCurriculum`
   - Uses the certified-chaining estimator envelope surface.
   - Shows calibrated selectors and out-of-envelope points.
5. `WM4IntrospectionCurriculum`
   - Uses the HOL introspection bridge for source, strength, exactness, and
     budget readouts.
   - Shows source-free failure and over-budget re-derivation rejection.
6. `LogicTowerCurriculum`
   - Uses the LC and BinaryEvidence bridge facts for the intuitionistic,
     Gödel-Dummett, and classical tower.
   - Separates the proved diagonal top-reflection fact from the still-missing
     single-chain-to-all-prelinear completeness bridge.

Import `Mettapedia.Examples.PLN` for the whole examples room, or import one
curriculum module directly when teaching a single rule family.
