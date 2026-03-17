import Mettapedia.Logic.LP.Core
import Mettapedia.Logic.LP.Substitution
import Mettapedia.Logic.LP.Matching
import Mettapedia.Logic.LP.Unification
import Mettapedia.Logic.LP.UnificationMGU
import Mettapedia.Logic.LP.MMMeasure
import Mettapedia.Logic.LP.UnificationComplete
import Mettapedia.Logic.LP.UnificationCompletenessCanaries
import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.SLD
import Mettapedia.Logic.LP.SLDCompute
import Mettapedia.Logic.LP.SLDAll
import Mettapedia.Logic.LP.SLDCompletenessKit
import Mettapedia.Logic.LP.SLDCompletenessCanaries
import Mettapedia.Logic.LP.PropositionalChainer
import Mettapedia.Logic.LP.PropositionalConnectionChainer
import Mettapedia.Logic.LP.FirstOrderConnectionTrace
import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.Logic.LP.FunctionFreeEvaluation
import Mettapedia.Logic.LP.CertifyingDatalogBridge
import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.LP.PathMapBridge
import Mettapedia.Logic.LP.OSLFBridge
import Mettapedia.Logic.LP.WorldModelBridge
import Mettapedia.Logic.LP.RangeRestriction

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
| `MMMeasure` | Global MM measures (`mmVarCount`,`mmSize`) + rule-wise decrease lemmas |
| `UnificationComplete` | Fuel-completeness bridges (`UnifyDerives`, success existence) |
| `UnificationCompletenessCanaries` | FO regression canaries (occurs-check boundary + semantic endpoint) |
| `Semantics` | T_P_LP, monotonicity, leastHerbrandModel (OrderHom.lfp), iteration |
| `SLD` | SLD resolution trees, grounding-substitution composition, soundness |
| `SLDCompute` | Executable DFS SLD resolution, bridge to SLDTree, soundness |
| `SLDAll` | All-solutions DFS SLD (flatMap), soundness, subsumes sldSearch |
| `SLDCompletenessKit` | Canonical lift-kit API (`hBase/hRule`) + concrete kit instances |
| `SLDCompletenessCanaries` | Concrete positive/negative completeness canaries |
| `FunctionFree` | Function-free fragment: GroundTerm ≃ constants, DecidableEq GroundAtom |
| `PropositionalConnectionChainer` | PeTTa-style connection tableau traces, checker soundness/completeness, refinement aliases |
| `FirstOrderConnectionTrace` | FO trace checker semantics (`proof_fo` shape), replay soundness theorem |
| `FunctionFreeEvaluation` | HerbrandBase, finiteness, leastModel = ⋃ T_P_LP_iter |
| `CertifyingDatalogBridge` | CDLGroundAtom ≃ GroundAtom (List↔Fin bridge) |
| `Provenance` | K-relations, T_P_K_LP, semiring homomorphism theorem |
| `PathMapBridge` | Conjunctive queries, evidence counting, monotonicity |
| `OSLFBridge` | Ground atom → Pattern encoding, FinInterpretation → RelationEnv |
| `WorldModelBridge` | LP least model → BinaryWorldModel evidence, monotonicity |
| `RangeRestriction` | `isUnit`, `isRangeRestricted`, unit-KB LHM characterization |
-/
