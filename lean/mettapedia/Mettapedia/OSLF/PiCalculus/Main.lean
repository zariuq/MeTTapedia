import Mettapedia.OSLF.PiCalculus.Syntax
import Mettapedia.OSLF.PiCalculus.StructuralCongruence
import Mettapedia.OSLF.PiCalculus.Reduction
import Mettapedia.OSLF.PiCalculus.MultiStep

/-!
# π-Calculus Formalization

Main entry point that re-exports all π-calculus modules.

## Contents
- Syntax: Process syntax and names
- StructuralCongruence: α-equivalence and ≡ relation
- Reduction: Operational semantics
- MultiStep: Reflexive-transitive closure of reduction

## Future Work
- Bisimulation: Behavioral equivalence
- RhoEncoding: Encoding π → ρ (Lybech 2022)
- SeparationTheorem: Proof that π ⊄ ρ (Lybech 2022, Theorem 1)
-/
