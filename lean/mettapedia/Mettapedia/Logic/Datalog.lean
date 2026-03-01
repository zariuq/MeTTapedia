import Mettapedia.Logic.LP

/-!
# Datalog (Retired → LP)

The standalone Datalog formalization has been retired. LP (Logic Programming)
is the single semantic core; Datalog = LP restricted to function-free signatures.

All Datalog functionality is now available through the LP module:

| Old Datalog | LP Equivalent |
|---|---|
| `Core` (Signature, Term, Atom, Rule, KB) | `LP.Core` (LPSignature, Term, Atom, Clause, KB) |
| `Substitution` (Grounding, applyAtom) | `LP.Substitution` (Grounding, Subst) |
| `Semantics` (T_P, leastModel) | `LP.Semantics` (T_P_LP, leastHerbrandModel) |
| `Evaluation` (HerbrandBase, finiteness) | `LP.FunctionFreeEvaluation` |
| `Provenance` (K-relations, T_P_K) | `LP.Provenance` (KRelation, T_P_K_LP) |
| `PathMapBridge` (DatalogQuery, evidence) | `LP.PathMapBridge` (LPQuery, evidence) |
| `OSLFBridge` (datalogToRelEnv) | `LP.OSLFBridge` (lpToRelEnv) |
| `WorldModelBridge` (evidence monotonicity) | `LP.WorldModelBridge` |
| `Embedding` (Datalog ⊂ LP) | `LP.CertifyingDatalogBridge` (CDLGroundAtom ≃ GroundAtom) |

Original files archived at `Mettapedia/_archive/Datalog/`.
-/
