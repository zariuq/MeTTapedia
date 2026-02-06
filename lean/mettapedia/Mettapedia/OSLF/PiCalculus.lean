import Mettapedia.OSLF.PiCalculus.Syntax
import Mettapedia.OSLF.PiCalculus.StructuralCongruence
import Mettapedia.OSLF.PiCalculus.Reduction
import Mettapedia.OSLF.PiCalculus.MultiStep
import Mettapedia.OSLF.PiCalculus.RhoEncoding
import Mettapedia.OSLF.PiCalculus.RhoEncodingCorrectness

/-!
# π-Calculus

Asynchronous, choice-free π-calculus with atomic names.

## References
- Lybech (2022): "Encodability and Separation for a Reflective Higher-Order Calculus"

## Current Status

### Phase 1 COMPLETE ✅ (Zero Sorries)
- ✅ Syntax: Process inductive type with atomic names
- ✅ Structural congruence: α-equivalence and structural laws
- ✅ Reduction semantics: COMM rule and congruence rules
- ✅ Multi-step reduction: Reflexive-transitive closure
- ✅ substitute_freeNames: Substitution affects free names (all cases PROVEN)
- ✅ substitute_freeNames_reverse: Reverse inclusion for fresh substitution
- ✅ substitute_freeNames_fresh: Equality for alpha-conversion
- ✅ freeNames_eq: Structural congruence preserves free names (all cases PROVEN)
- ✅ freeNames_reduces: Reduction preserves/reduces free names (PROVEN)

### Phase 2 ENCODING COMPLETE ✅ (Zero Sorries)
- ✅ piNameToRhoName: Map π-names to ρ-names (quoted variables)
- ✅ rhoNil, rhoPar, rhoInput, rhoOutput: ρ-calculus constructors
- ✅ dropOperation: D(x) - continuously offers x for communication
- ✅ nameServer: Lybech's name server with fresh name generation
- ✅ encode: Encoding function ⟦P⟧_{n,v} for all 6 π-calculus constructors
- ✅ fullEncode: Complete encoding with name server running in parallel

### Phase 2b: Correctness Proofs (6 sorries, 0 axioms) ✅
- ✅ RhoBisimilar: Prop-valued bisimulation using Nonempty wrapper
- ✅ Observable output definitions (PiObservableOutput, RhoObservableOutput)
- ✅ Divergence definitions (PiDiverges, RhoDiverges)
- ⚠️ Proposition 1 (parameter independence): 1 sorry [SEMANTIC - needs bisimulation proof]
- ✅ **Proposition 2 (substitution invariance): FULLY PROVEN! (0 axioms, 0 sorries)**
  - ✅ Main theorem proven for ALL 6 process constructors
  - ✅ Freshness conditions as theorem hypotheses (Lybech page 106):
    - `h_fresh_u_P : u ∉ P.names` and `h_fresh_w_P : w ∉ P.names` (process freshness)
    - `h_fresh_u : u ∉ [n, v]` and `h_fresh_w : w ∉ [n, v]` (parameter freshness)
    - `h_disjoint_u : NamespaceDisjoint u n` and `h_disjoint_w : NamespaceDisjoint w n` (namespace freshness)
  - ✅ NamespaceDisjoint: Definition (not axiom!) capturing Lybech's `u # N[n]` (page 106)
    - `NamespaceDisjoint u n := ∀ suffix, u ≠ n ++ suffix`
    - Propagation lemma: `namespace_disjoint_derived` (PROVEN)
  - ✅ fresh_derived_param: PROVEN using NamespaceDisjoint
  - Key techniques:
    - toListRepr/fromListRepr algebraic reformulation for pattern matching
    - if_neg for parameter freshness simplification
    - String.append_assoc for derived parameter associativity
    - Namespace disjointness propagation for recursive calls
- ⚠️ Proposition 3 (observational correspondence): 3 sorries [SEMANTIC]
  - 2 sorries: Helper lemmas (rhoPar_POutput_left, encode_par_output_creates_POutput)
  - 1 sorry: Main theorem (depends on Prop 4 operational correspondence)
- ⚠️ Proposition 4 (operational correspondence): 1 sorry [SEMANTIC - simulation proof]
- ⚠️ Proposition 5 (divergence reflection): 1 sorry [SEMANTIC - trace-based reasoning]

**Zero axioms** - all preconditions properly expressed as theorem hypotheses!

### Next Phases
- Complete Phase 2b: Finish Propositions 2-5
- Phase 3: Separation theorem (π ⊄ ρ) - Lybech's Theorem 1
- Phase 4: Connection to linear logic via session types (future project)
-/
