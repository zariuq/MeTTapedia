# PLN bridges to logic

This directory contains PLN-facing bridges from logical semantics into evidence
and world-model interfaces.

## Entry points

- `PLNIntuitionisticBridge`
  - Defines the propositional BinaryEvidence semantics.
  - Proves BinaryEvidence validates Dummett prelinearity and refutes Boolean
    excluded middle.
  - Provides the diagonal embedding from the standard Gödel chain into
    BinaryEvidence and proves top reflection.
- `BooleanHeytingBridge`
  - Relates Boolean and Heyting readouts where the algebraic structure permits
    it.
- `WorldModel`
  - Collects logic-to-world-model bridge interfaces.

## LC status

The LC bridge currently uses the proven LO completeness theorem for consequence
over all prelinear Heyting-valued models.  The diagonal facts show how a
single-chain countermodel reflects through BinaryEvidence, but the missing
bridge is the theorem that validity in that single chain implies consequence
over all prelinear models.  `LogicTowerCurriculum` exposes the proved tower
facts without strengthening them.

Use `Mettapedia.PLN.Bridges.Logic` to import the logic bridge barrel.
