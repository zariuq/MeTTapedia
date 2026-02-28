import Mettapedia.Logic.Datalog.Core
import Mettapedia.Logic.Datalog.Substitution
import Mettapedia.Logic.Datalog.Semantics
import Mettapedia.Logic.Datalog.Evaluation
import Mettapedia.Logic.Datalog.Provenance
import Mettapedia.Logic.Datalog.PathMapBridge
import Mettapedia.Logic.Datalog.OSLFBridge
import Mettapedia.Logic.Datalog.WorldModelBridge
import Mettapedia.Logic.Datalog.Embedding

/-!
# Datalog Formalization

Barrel import for the Datalog module stack:

| File | Contents |
|------|----------|
| `Core` | Signature, Term, Atom, Rule, KnowledgeBase, GroundAtom |
| `Substitution` | Grounding, applyAtom, groundBodySatisfied |
| `Semantics` | T_P operator, leastModel (OrderHom.lfp), fixpoint theorems |
| `Evaluation` | HerbrandBase, finiteness, iteration completeness |
| `Provenance` | SemiringWithMonus, K-relations, T_P_K, homomorphism theorem |
| `PathMapBridge` | DatalogQuery, evidence counting, leastModel monotonicity |
| `OSLFBridge` | datalogToRelEnv, mem_datalogToRelEnv, leastModelRelEnv |
| `WorldModelBridge` | datalogModelEvidence, monotonicity, EDB positivity |
-/
