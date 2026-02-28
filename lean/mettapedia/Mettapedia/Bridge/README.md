# Bridge

Mettapedia/Bridge connects cross-module formalizations.

## Files

- `BitVectorEvidence.lean`
  - BitVectorEvidence.lean provides a geometric semantics for PLN evidence

Positive and negative evidence counts correspond to known bits in partial bit vectors.
Unknown bits give a combinatorial interpretation of uncertainty.

## Key results

- completions_card: `|completions|(v) = 2^(countUnknown(v))`
- completions_mean_weight: `"average Hamming weight" = pos + unknown / 2 / n`
- toEvidence_strength: `Evidence.strength = "expected fraction of 1s"`

- completions_card is |completions(v)| = 2^(countUnknown v).
- completions_mean_weight is average Hamming weight = (pos + unknown/2) / n.
- toEvidence_strength is Evidence.strength = expected fraction of 1s.
- This bridge connects discrete evidence to continuous Beta distribution theory.

## Status

- This directory doesn't contain sorries.
