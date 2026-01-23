/-
# Separation Machinery (Index Module)

This module groups the separation-related developments:

- `Additive/Axioms/SandwichSeparation.lean`: the iterate/power "sandwich" axiom (`KSSeparation`) on the
  core base structure, proving commutativity and Archimedean-style consequences.
- `Additive/Axioms/AnomalousPairs.lean`: the "no anomalous pairs" condition from ordered semigroup theory.
- `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`: Hölder embedding approach to the representation theorem
  (uses Eric Luap's OrderedSemigroups library).

**Archived**:
- `_archive/Separation/Derivation.lean`: experimental attempt to derive `KSSeparation` from structured
  hypotheses (superseded by the Hölder approach).
- `_archive/Separation/AlimovEmbedding.lean`: earlier partial Alimov embedding attempt (superseded
  by HolderEmbedding.lean which uses Eric Luap's proven theorems).
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.AnomalousPairs
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding
