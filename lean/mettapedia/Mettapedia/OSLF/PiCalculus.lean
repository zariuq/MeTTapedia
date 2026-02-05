import Mettapedia.OSLF.PiCalculus.Syntax
import Mettapedia.OSLF.PiCalculus.StructuralCongruence
import Mettapedia.OSLF.PiCalculus.Reduction
import Mettapedia.OSLF.PiCalculus.MultiStep

/-!
# π-Calculus

Asynchronous, choice-free π-calculus with atomic names.

## References
- Lybech (2022): "Encodability and Separation for a Reflective Higher-Order Calculus"

## Current Status (Phase 1)
- ✅ Syntax: Process inductive type with atomic names
- ✅ Structural congruence: α-equivalence and structural laws
- ✅ Reduction semantics: COMM rule and congruence rules
- ✅ Multi-step reduction: Reflexive-transitive closure
- ✅ Main theorem: Reduction preserves/reduces free names (PROVEN modulo helpers)

## Remaining Work
- ⚠️ 6 sorries in helper lemmas:
  1. `Process.substitute_freeNames`: Substitution affects free names correctly
  2. `StructuralCongruence.freeNames_eq`: 5 cases (nu_par, nu_swap, 3 α-conversions)

## Next Phases
- Phase 2: Lybech's correct π → ρ encoding with name server pattern
- Phase 3: Separation theorem (π ⊄ ρ)
- Phase 4: Connection to linear logic via session types (future project)
-/
