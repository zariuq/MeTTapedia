# MeTTa Language Formalization

Kernel-checked Lean 4 formalization of the [MeTTa](https://metta-lang.dev/) language family.
Four layers, each with its own proof obligations and trust model.

- Language spec: https://trueagi-io.github.io/hyperon-experimental/metta/
- Main site: https://metta-lang.dev/

| Layer | Dir | What it is |
|-------|-----|------------|
| Computable spec | `HE/` | Fuel-bounded interpreter from `interpreter.rs` + `metta.md`; 37 conformance theorems |
| Pure metatheory | `Pure/` | Typed pure MeTTa; subject reduction and confluence proven |
| Prolog evaluation | `PeTTa/` | PeTTa evaluation pipeline; LP soundness and bridge theorems |
| OSLF instance | `Core/` | Full-language OSLF `LanguageDef` (state-indexed, legacy) |

Supporting:
- `PureKernel/` — declaration kernel (inductive types as MeTTa atoms)
- `SpecProfiles/` — profile specifications
- `SuiteBase/` — shared test suite base
- `TensorDSL/` — tensor operation layer

Root-level modules (`RuntimeSpec.lean`, `ExecutionContract.lean`,
`ElaboratedCore.lean`, etc.) are integration facades — they wire the
layers together and export a unified surface for the rest of Mettapedia.

```bash
ulimit -v 6291456 && lake build Mettapedia.Languages.MeTTa
```
