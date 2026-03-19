import Mettapedia.Logic.BDD.ProbMeTTaBridge

/-!
# ProbLog: Probabilistic Logic Programming — Formal Specification

This file serves as the **landing page** for the ProbLog formalization.
It defines nothing new — all definitions and theorems are in the imported modules.
Read this file first, then follow the imports for details.

## What is ProbLog?

ProbLog (De Raedt, Kimmig, Toivonen, IJCAI 2007) is a probabilistic extension of
Prolog. A ProbLog program consists of:

1. **Probabilistic facts**: `pᵢ :: fᵢ` — each ground atom `fᵢ` is independently true
   with probability `pᵢ ∈ [0,1]`. These are the random variables.

2. **Definite clauses** (rules): `head :- body₁, ..., bodyₖ` — standard Horn clauses
   that derive new atoms from existing ones.

3. **Queries**: `query(q)` — what is the probability that ground atom `q` is derivable?

### Example: Alarm Network

```
0.1 :: burglary.        -- P(burglary) = 0.1
0.2 :: earthquake.      -- P(earthquake) = 0.2
alarm :- burglary.      -- alarm if burglary
alarm :- earthquake.    -- alarm if earthquake
query(alarm).           -- P(alarm) = ?
```

Answer: P(alarm) = 1 - (1 - 0.1)(1 - 0.2) = 0.28

## Distribution Semantics (Sato 1995)

ProbLog defines query probability via the **distribution semantics**:

1. A **total choice** `a : Fin n → Bool` independently assigns each probabilistic
   fact to true or false.

2. The **weight** of total choice `a` is:
   ```
   weight(a) = Π_{i=1}^{n} (if aᵢ then pᵢ else 1-pᵢ)
   ```

3. The **residual program** for total choice `a` consists of the original rules
   plus the probabilistic facts that were chosen true.

4. Query `q` **holds under `a`** iff `q` is in the **least Herbrand model** of
   the residual program.

5. The **query probability** is the weighted sum over total choices:
   ```
   P(q) = Σ_{a : total choice} weight(a) · [q holds under a]
   ```

## Lean Formalization

### Core definitions (in `ProbLogCompilation.lean`)

- `ProbLogProgram σ n` — a ProbLog program: `n` probabilistic facts + definite clauses
- `residualKB prog w` — residual knowledge base for world `w`
- `queryHolds prog q w` — query `q` holds in world `w` (via least Herbrand model)

### Assignment-based definitions (in `BDD/Compilation.lean`)

- `residualKBa prog a` — residual KB for total choice `a : Fin n → Bool`
- `queryHoldsA prog q a` — query `q` holds under total choice `a`

### BDD-based computation (in `BDD/`)

ProbMeTTa compiles ProbLog queries to BDDs (Fierens et al. 2015) and computes
probabilities via Weighted Model Counting (Bryant 1986):

- `BDD n` — Binary Decision Diagram over `n` Boolean variables
- `BDD.eval f a` — evaluate BDD under assignment `a`
- `bdd_wmc f env` — Weighted Model Counting
- `GroundBDDCompile prog q f` — compilation from ProbLog query to BDD

### Proven theorems (all 0 sorry)

| Theorem | File | Statement |
|---------|------|-----------|
| `bdd_wmc_correct` | `BDD/WMC.lean` | WMC = weighted sum over satisfying assignments |
| `apply_eval` | `BDD/Operations.lean` | BDD apply preserves Boolean semantics |
| `GroundBDDCompile_sound` | `BDD/Compilation.lean` | BDD true ⟹ query holds (soundness) |
| `queryStrength_prop_eq_queryProb` | `ProbLogDistributionSemantics.lean` | WM-PLN extraction = ProbLog probability |
| `compilation_or_noisyOr` | `ProbLogCompilation.lean` | OR-pattern ProbLog = noisy-OR formula |
| `fuzzyOrMulti_eq_noisyOrMulti` | `PLNNoisyOr.lean` | PLN fuzzy-OR = noisy-OR |

### Conformance tests (kernel-checked, `BDD/Operations.lean`)

| Program | Boolean function | Verified |
|---------|-----------------|----------|
| Alarm (2 vars) | `v₀ ∨ v₁` | `by simp` |
| Conjunction (2 vars) | `v₀ ∧ v₁` | `by simp` |
| Negation (1 var) | `¬v₀` | `by simp` |
| Neg-conjunction (2 vars) | `v₀ ∧ ¬v₁` | `by simp` |
| Overlapping rules (3 vars) | `(v₀ ∧ v₁) ∨ v₂` | `by simp` |
| Fever chain (5 vars) | `(v₂ ∧ v₃) ∨ ((v₀ ∨ v₁) ∧ v₂ ∧ v₄)` | `by simp` |
| Calls-mary (3 vars) | `(v₀ ∨ v₁) ∧ v₂` | `by simp` |

## References

- De Raedt, Kimmig, Toivonen. "ProbLog: A Probabilistic Prolog and its Application
  in Link Discovery." IJCAI 2007.
- Sato. "A Statistical Learning Method for Logic Programs with Distribution
  Semantics." ICLP 1995.
- Fierens, Van den Broeck, Renkens, Shterionov, Gutmann, Thon, Janssens, De Raedt.
  "Inference and Learning in Probabilistic Logic Programs using Weighted Boolean
  Formulas." TPLP 2015.
- Bryant. "Graph-Based Algorithms for Boolean Function Manipulation." IEEE TC 1986.
- Van Emden, Kowalski. "The Semantics of Predicate Logic as a Programming Language."
  JACM 1976.
-/

-- Re-export key definitions for convenient access
namespace Mettapedia.Logic.ProbLogSpec

open Mettapedia.Logic.LP
open Mettapedia.Logic.ProbLogCompilation
open Mettapedia.Logic.ProbLogDistributionSemantics
open Mettapedia.Logic.BDDCore

/-! ## Quick Reference

The main types and functions, gathered for convenience:

- **Program**: `ProbLogProgram σ n` — n probabilistic facts + definite clauses
- **Semantics**: `queryHoldsA prog q a` — does query hold under total choice a?
- **Probability**: `weightedSat φ env` — distribution semantics probability
- **BDD**: `bdd_wmc f env` — BDD-based probability computation
- **Compilation**: `GroundBDDCompile prog q f` — compile query to BDD
- **Correctness**: `bdd_wmc_correct` — WMC = distribution semantics
- **Soundness**: `GroundBDDCompile_sound` — compiled BDD reflects query truth
-/

end Mettapedia.Logic.ProbLogSpec
