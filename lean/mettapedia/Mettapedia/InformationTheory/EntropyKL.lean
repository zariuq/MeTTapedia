import Mettapedia.InformationTheory.ShannonEntropy.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Main

/-!
# Unified Entropy + KL (Curated Entry Point)

This file is a **single import** that puts the main finite-discrete entropy / KL stories on the
same page:

1. **Axiomatic entropy** (Faddeev 1956, Shannon 1948, Shannon–Khinchin 1957):
   `Mettapedia/InformationTheory/ShannonEntropy/*`
2. **Knuth–Skilling derivation** (Appendix C → divergence → entropy on `ProbDist`):
   `Mettapedia/ProbabilityTheory/KnuthSkilling/Information/*`
3. **Bridges** between representations and between discrete and measure-theoretic KL:
   `Mettapedia/InformationTheory/ShannonEntropy/Interface.lean`
   `Mettapedia/InformationTheory/ShannonEntropy/MeasureTheoreticBridge.lean`

## What to import

- For a reviewer-friendly K&S-only entrypoint (Appendices A/B/C + σ-additivity + probability + entropy):
  `import Mettapedia.ProbabilityTheory.KnuthSkilling.FoundationsOfInference`

- For "entropy/KL from *all* routes":
  `import Mettapedia.InformationTheory.EntropyKL`

## Canonical objects + bridge theorems

The finite distribution types used throughout the project are:

- `ProbVec n` (mathlib `stdSimplex` based), defined in `Mettapedia/InformationTheory/Basic.lean`
- `ProbDist n` (foundations-level finite distributions), defined in
  `Mettapedia/ProbabilityTheory/Foundations/Distributions/ProbDist.lean`
  and re-exported (as a KS-facing alias) in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/Information/InformationEntropy.lean`

The main equivalence glue lives in:

- `Mettapedia.InformationTheory.probVecEquivProbDist`
- `Mettapedia.InformationTheory.shannonEntropy_eq_ks_shannonEntropy`
- `Mettapedia.InformationTheory.klDivergenceVec` and `..._eq_klDiv` (measure bridge)

This file intentionally does not re-export names; it is an "import surface" with a single,
stable path that other subprojects (Cox, Shore–Johnson, etc.) can depend on.
-/

