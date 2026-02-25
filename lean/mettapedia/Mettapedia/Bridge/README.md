# Mettapedia/Bridge

Cross-module bridges connecting different formalizations.

## Files

### BitVectorEvidence.lean

Geometric semantics of PLN Evidence through bit vectors. PLN Evidence counts
(positive, negative) correspond to known bits in partial bit vectors; unknown
bits give a combinatorial interpretation of uncertainty.

Key results:
- `completions_card`: |completions(v)| = 2^(countUnknown v)
- `completions_mean_weight`: average Hamming weight = (pos + unknown/2) / n
- `toEvidence_strength`: Evidence.strength = expected fraction of 1s

Bridges discrete (natural number) evidence to continuous (real) PLN distributional
theory via the Beta distribution.

Zero sorries.
