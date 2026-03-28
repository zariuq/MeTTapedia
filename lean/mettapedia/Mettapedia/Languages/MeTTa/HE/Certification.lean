import Mettapedia.Languages.MeTTa.HE.Correctness

/-!
# Hyperon Experimental MeTTa Certification Boundary

This module is the light public entry point for the verified HE evaluator
certificate surface.

## Exported Boundary

The lasting top-level artifact is:

- `EvalAtomCertified`

and the minimal executable witness boundary just below it is:

- `EvalAtomStablyReaches`

with its headline public consequences:

- `evalAtomStablyReaches_to_EvalAtom`
- `evalAtomStablyReaches_to_certified`
- `evalAtomCertified_to_EvalAtom`
- `evalAtomCertified_iff_stably_reaches`
- `evalAtomCertified_to_filtered_witness`

## Design

The additive implementation-refined spec boundary is defined in
`ExecutableBoundary.lean`, while the large proof transport stack stays in
`Correctness.lean`:

- `EvalAtomStablyReaches`
- `EvalAtomCertified`
- evaluator exactness against the private sync mirror
- aligned eventual bridge machinery
- conformance counterexamples ruling out stronger false boundaries

This file intentionally adds no new semantics. It provides a stable, lighter
module boundary for users who want the refined HE certificate surface without
reading the full internal proof development first.

## Auditor Note

Positive example:
- `EvalAtomCertified` means a top-level HE evaluation result has both
  declarative meaning and stable executable support from some fuel onward.

Negative example:
- a coarse `EvalAtom` derivation may still be a low-fuel transient result and
  therefore fail to be certified; see the regression in `Conformance.lean`.
-/
