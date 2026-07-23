# PLN bridges to HOL

This directory contains PLN readout and world-model bridges over the HOL
derivation-tree infrastructure.

## Entry points

- `ProvenanceSemiringReadout`
  - Defines `DerivationTree`, `sourceSupport`, `SourceDisjoint`, tree bags,
    source ideals, and closed-theory tree witnesses.
- `BinaryEvidenceReadout`
  - Grades HOL derivation trees as positive `BinaryEvidence`.
  - Defines `LedgerBackedTree`, `support_exact`, and the ledger-backed
    disjointness bridge back to `DerivationTree.SourceDisjoint`.
- `Introspection`
  - Provides query readouts for why, how strongly, what breaks, and whether a
    proof is worth re-deriving under a budget.
- `LedgerMultiPathAdapter`
  - Encodes ledger-backed HOL source tokens into `Finset Nat` source sets.
  - Instantiates the multipath T-A dependency equation through
    `ledgerBackedTree_unionMeasure_eq_add_sub_dependency` and
    `ledgerBackedTree_unionMeasure_eq_add_sub_overlapProduct`.

Use `Mettapedia.PLN.Bridges.HOL` to import the standard HOL bridge barrel.
