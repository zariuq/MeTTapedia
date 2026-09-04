# Probabilistic Logic Networks

This directory contains PLN evidence carriers, truth-value theories,
inference rules, world models, inference control, and their proved bridges to
neighboring mathematics.

- `Evidence/` contains PLN evidence carriers and revision mathematics.
- `TruthValues/` contains scalar, interval, distributional, and related
  readouts and their comparison theorems.
- `RuleFamilies/` contains inference-rule semantics.
- `WorldModel/` contains world-model interpretations.
- `InferenceControl/` contains certified chaining and premise-selection work.
- `Bridges/` relates PLN to probability theory, logic, GSLT, HOL, knowledge
  representation, and other domains.
- `Comparisons/` contains PLN-centered comparisons rather than ownership of
  the compared systems.

PLN and NARS are sibling formalizations. They share source-neutral evidence
geometry through `Mettapedia.Evidence`, while all PLN--NARS claims live in
`Mettapedia.NARS.Bridges.PLN` and retain both agreement and obstruction
theorems.

