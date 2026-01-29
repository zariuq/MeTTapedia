import Mettapedia.ProbabilityTheory.KnuthSkilling.Core
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.ScaleCompleteness
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Variational.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityCalculus
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Main

/-!
# Foundations of Inference (Reviewer Entrypoint)

This is a curated entrypoint for the Knuth–Skilling *Foundations of Inference* development.

## Primary Assumption: NoAnomalousPairs (NAP)

The canonical proof path for Appendix A uses **`NoAnomalousPairs`** from the 1950s ordered-semigroup
literature (Alimov 1950, Fuchs 1963), formalized via Eric Luap's OrderedSemigroups library.

- `NoAnomalousPairs` is identity-free; `KSSeparation` requires identity
- Under `IdentIsMinimum`: **NAP ⟺ KSSeparation** (full equivalence!)
  - Forward: `KSSeparation + IdentIsMinimum ⇒ NoAnomalousPairs` (AnomalousPairs.lean)
  - Reverse: `NoAnomalousPairs ⇒ ℝ embedding ⇒ KSSeparation` (HolderEmbedding + AxiomSystemEquivalence)
- Historical precedent: NAP predates K&S by 60+ years (Alimov 1950)

See `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean` for the canonical proof.

## What This Imports

- the core axiom hierarchy (`KSSemigroupBase` → `KnuthSkillingMonoidBase` → `KnuthSkillingAlgebraBase`),
- Appendix A (additive representation via NAP/Hölder),
- Appendix B (product theorem),
- Appendix C (variational theorem),
- the σ-additivity bridge (`Core/ScaleCompleteness.lean`),
- the derived probability calculus and information/entropy layer.

It does **not** import Shore–Johnson (first-class but import explicitly), Cox, or hypercube material.
-/
