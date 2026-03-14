# HE — Hyperon Experimental Interpreter

Canonical computable specification of the [Hyperon Experimental](https://trueagi-io.github.io/hyperon-experimental/metta/)
MeTTa interpreter, directly from `interpreter.rs` and `metta.md` (lines 240–552).

**Source precedence:** `interpreter.rs` (ground truth) > `metta.md` (spec prose)

## Core

`Interpreter.lean` — 6 mutually recursive fuel-bounded functions:

| Function | Role |
|----------|------|
| `metta` | Top-level entry; dispatches on expression form |
| `interpretExpression` | Evaluates a single expression |
| `interpretFunction` | Handles function application |
| `interpretArgs` | Evaluates argument lists |
| `interpretTuple` | Evaluates tuple forms |
| `mettaCall` | Calls into the space / rule lookup |

`Types.lean` — `Bindings` (assignments + equalities), `ResultPair`, `ResultSet`, error codes.

`Conformance.lean` — 37 kernel-checked theorems (all `rfl` or `decide`),
clause-by-clause against `metta.md`. Zero axioms, zero sorry.

## Supporting Modules

| Module | Contents |
|--------|----------|
| `Space.lean` | `List Atom` space (computable, unlike Core's noncomputable `Multiset`) |
| `Matching.lean` | Pattern matching and binding unification |
| `TypeCheck.lean` | Type-checking pass |
| `CoreFragment.lean` | Core expression fragment |
| `HELanguageDef.lean` | Full OSLF `LanguageDef` with HE dispatch |
| `HEPremises.lean` | Premise specifications |
| `ContractCatalog.lean` | Execution contracts |

## Key semantics

- Symbols → `typeCast` (not equation lookup)
- Expressions → `interpretExpression` → `mettaCall`
- `Bindings`: `assignments : List (String × Atom)` + `equalities : List (String × String)`

```bash
ulimit -v 6291456 && lake build Mettapedia.Languages.MeTTa.HE
```
