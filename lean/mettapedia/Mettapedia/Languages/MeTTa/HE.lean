import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.TypeCheck
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import Mettapedia.Languages.MeTTa.HE.SyntaxSpec
import Mettapedia.Languages.MeTTa.HE.Conformance
import Mettapedia.Languages.MeTTa.HE.Properties
import Mettapedia.Languages.MeTTa.HE.DeclarativeSpec
import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.ExecutionContract
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR
import Mettapedia.Languages.MeTTa.HE.RewriteIRV2
import Mettapedia.Languages.MeTTa.HE.CoreFragment

/-!
# Hyperon Experimental MeTTa Semantics

Authoritative Lean 4 formalization of the HE MeTTa evaluation specification.

## Source of Truth
1. `https://trueagi-io.github.io/hyperon-experimental/metta/` (spec)
2. Conformance with `metta` CLI (conda hyperon environment)

## Module Structure
- `Types` — Error codes, Bindings (assignments + equalities), ResultSet
- `Space` — Atomspace queries, grounded dispatch
- `Matching` — match_atoms, merge_bindings, match_types (computable)
- `TypeCheck` — type_cast, check_argument_type (computable)
- `EvalSpec` — **Declarative spec**: mutual inductive relations for
               metta, interpretExpression, interpretFunction,
               interpretArgs, interpretTuple, mettaCall
- `MinimalMeTTa` — Stateful minimal instruction spec (match, add-atom, chain, etc.)
- `SyntaxSpec` — Authoritative HE syntax profiles
- `Conformance` — Derivation-tree conformance witnesses
- `Properties` — Universal theorems by induction on derivations
- `DeclarativeSpec` — Unified spec surface (clause forms, examples, audit index)

## Key Design Decisions
- Declarative inductive relations (no fuel, nondeterminism-native)
- Computable leaf operations (Matching, TypeCheck) for kernel-checked tests
- HE.Bindings with assignments + equalities (faithful to spec)
- Separate from PeTTa and MeTTaCore (no cross-contamination)
-/
