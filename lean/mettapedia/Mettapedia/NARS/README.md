# NARS

This directory contains source-faithful formalizations of the Non-Axiomatic
Reasoning System as a subject in its own right.

- `Logic/` contains NARS term and inheritance semantics.
- `TruthFunctions.lean` contains the numerical truth-value operations.
- `Evidence/` retains inference paths and source scopes, including productive
  path-dependent incoherence and the revision-versus-choice guard.
- `Control/` contains OpenNARS for Applications control and resource laws.
- `Bridges/` states proved relationships to PLN, probability theory,
  cognitive architectures, and universal-agent models.

NARS is not a subtheory of PLN. Both systems import neutral evidence geometry
from `Mettapedia.Evidence`; their numerical agreements and semantic
differences are then established in bridge modules.

