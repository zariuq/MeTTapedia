import OrderedSemigroups

/-!
# Ordered Semigroups

This module contains the formalization of ordered semigroups and the Hölder embedding theorem.

## Attribution

This code is adapted from Eric Luap's OrderedSemigroups formalization:
- **Source**: github.com/ericluap/OrderedSemigroups
- **License**: Apache 2.0
- **Adapted for**: Mettapedia project, Lean 4.25.0 / Mathlib v4.25.0

## Main Results

- `anomalous_pair`: Definition of anomalous pairs in ordered semigroups
- `not_anomalous_pair_commutative`: No anomalous pairs implies commutativity
- `not_anomalous_arch`: No anomalous pairs implies Archimedean property
- `holder_not_anom`: Hölder embedding theorem - ordered semigroup without anomalous pairs
  embeds into the reals

## References

- Luap, E. (2024). "OrderedSemigroups: Formalization of Ordered Semigroups in Lean 4."
- Alimov, N. G. (1950). "On ordered semigroups" (in Russian)
- Hölder, O. (1901). "Die Axiome der Quantität und die Lehre vom Mass"

## Import note

This file re-exports Eric Luap’s library as the local Lake dependency `ordered_semigroups`
(see `lakefile.toml`). The canonical module prefix is `OrderedSemigroups.*` (not
`Mettapedia.Algebra.OrderedSemigroups.*`).
-/
