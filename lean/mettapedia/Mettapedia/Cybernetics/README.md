# Cybernetics

This directory develops reusable mathematics of observation, distinction,
closure, constrained variety, individuation, and trace-mediated coordination.
The definitions are deliberately independent of any particular cognitive
architecture, logic, or runtime; application-specific modules import them and
prove instance theorems.

- `ObservedVariety.lean` treats an observer as a map from states to views. Its
  image type is the informative notion of observed variety; finite cardinality
  is a derived readout. Exact presentations preserve variety, while the
  micro/macro example proves that variety is observer-relative.
- `DistinctionConservation.lean` defines preservation of a named source
  distinction by a target observation. For inequality it is equivalent to
  injectivity. The observer-indexed form permits only losses irrelevant to the
  declared observation.
- `RelationalClosure.lean` packages a network closure with extensivity,
  monotonicity, and idempotence, converts it to Mathlib's closure-operator
  interface, and retains proof-relevant receipts for generated connections.
- `Individuation.lean` separates a static individuated state from a composable
  process of becoming and from persistence of a protected observation.
- `ConstrainedVariety.lean` separates constraint, static variety, and dynamic
  variation, including the full eight-case classification and nontrivial
  positive and negative organizations.
- `Stigmergy.lean` formalizes action, agent, medium, trace, and coordination.
  Its delayed-episode definition requires a persistent trace; an ephemeral
  direct-coordination control therefore does not count as stigmergy.

The historical sources are Francis Heylighen's work on distinction
conservation (1989), relational closure (1990), constrained variation and
metasystem transitions (1995), and stigmergy (2015), together with David
Weinbaum and Viktoras Veitas on individuation and open-ended intelligence. The
Lean modules state which constructions are project extensions rather than
attributing later bridge theorems to those sources.

## Downstream bridges

- `Mettapedia.GSLT.Dynamics.AnswerDistinctionConservation` identifies answer
  distinction conservation with the independently defined faithfulness law and
  exhibits concrete order- and multiplicity-erasing transforms.
- `Mettapedia.Logic.MarkovLogicIndividuationBridge` recovers the existing
  WM-calculus individuation structures as instances of the general theory.
- `Mettapedia.Enactive.IndividuationGeneration` and
  `Mettapedia.Enactive.MetasystemTransition` give explicit conditions under
  which process or constrained variation warrants a new generation.
- `Mettapedia.Languages.MeTTa.StigmergicSpace` instantiates a stigmergic medium
  with a proof-relevant MeTTa space.

The conceptual overview and complete theorem/control map are in
`papers/open-ended-plural-intelligence.tex`.
