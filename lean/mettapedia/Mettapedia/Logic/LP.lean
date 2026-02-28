import Mettapedia.Logic.LP.Core
import Mettapedia.Logic.LP.Substitution
import Mettapedia.Logic.LP.Matching
import Mettapedia.Logic.LP.Unification
import Mettapedia.Logic.LP.UnificationMGU
import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.SLD
import Mettapedia.Logic.LP.SLDCompute

/-!
# Logic Programming Kernel

Barrel import for the LP module stack:

| File | Contents |
|------|----------|
| `Core` | LPSignature, Term, Atom, Clause, GroundTerm, GroundAtom, KnowledgeBase |
| `Substitution` | Subst, apply, compose, identity/composition laws, Grounding |
| `Matching` | collectBindings, matchTerm, matchAtom (one-sided unification) |
| `Unification` | Martelli-Montanari unification, occurs check, soundness proof |
| `UnificationMGU` | Most General Unifier property for Martelli-Montanari |
| `Semantics` | T_P_LP, monotonicity, leastHerbrandModel (OrderHom.lfp), iteration |
| `SLD` | SLD resolution trees, grounding-substitution composition, soundness |
| `SLDCompute` | Executable DFS SLD resolution, bridge to SLDTree, soundness |
-/
