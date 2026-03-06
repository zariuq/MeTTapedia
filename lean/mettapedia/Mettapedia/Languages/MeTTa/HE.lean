import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.TypeCheck
import Mettapedia.Languages.MeTTa.HE.Interpreter
import Mettapedia.Languages.MeTTa.HE.Conformance
import Mettapedia.Languages.MeTTa.HE.Properties
import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR

/-!
# Hyperon Experimental MeTTa Semantics

Authoritative Lean 4 formalization of the HE MeTTa interpreter algorithm.

## Source Precedence
1. `hyperon-experimental/lib/src/metta/interpreter.rs` (ground truth)
2. `hyperon-experimental/docs/metta.md` (spec prose)
3. `MeTTa specification - OpenCog Hyperon.pdf` (secondary)

## Module Structure
- `Types` - Error codes, Bindings (assignments + equalities), ResultSet
- `Space` - Atomspace queries, grounded dispatch
- `Matching` - match_atoms, merge_bindings, match_types
- `TypeCheck` - type_cast, check_argument_type, check_if_function_type_is_applicable
- `Interpreter` - metta, interpretExpression, interpretFunction,
                  interpretArgs, interpretTuple, mettaCall
- `Conformance` - Clause-by-clause theorem matrix (37 proven theorems)
- `Properties` - Structural properties (fuel zero, passthrough, etc.)

## Key Design Decisions
- Fuel-bounded termination (total, kernel-checkable)
- HE.Bindings with assignments + equalities (faithful to spec)
- Separate from PeTTa and MeTTaCore (no cross-contamination)
- OSLF/GSLT bridge is a derived adapter (not in this module)
-/
