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
import Mettapedia.Logic.LP.BackwardViaForward
import Mettapedia.Logic.LP.BackwardViaForwardMP
import Mettapedia.Logic.LP.PropositionalConnectionChainer
import Mettapedia.Logic.LP.PropositionalConnectionControls
import Mettapedia.Logic.LP.FirstOrderConnectionTrace
import Mettapedia.Logic.LP.FirstOrderConnectionControls
import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.Logic.LP.FunctionFreeEvaluation
import Mettapedia.Logic.LP.CertifyingDatalogBridge
import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.LP.PathMapBridge
import Mettapedia.Logic.LP.RangeRestriction
import Mettapedia.Logic.LP.Narrowing
import Mettapedia.Logic.LP.NarrowingLift
import Mettapedia.Logic.LP.LinearUnification
import Mettapedia.Logic.LP.HypotheticalPropositional
import Mettapedia.Logic.LP.Runtime

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
| `BackwardViaForward` | Nil-style demand materialization: backward chaining via propositional forward chaining |
| `PropositionalConnectionChainer` | Branch-local replay/search, operational correspondence and independent Boolean unsatisfiability |
| `PropositionalConnectionControls` | Satisfiable sibling-leak counterexample, genuine sibling and ancestor proofs, all-fuel search rejection |
| `FirstOrderConnectionTrace` | Branch-local FO replay/search and fixed-variable operational correspondence; per-use freshening is separate |
| `FirstOrderConnectionControls` | Generic sibling-restoration rejection and substitution through separate ancestor paths |
| `FunctionFreeEvaluation` | HerbrandBase, finiteness, leastModel = ⋃ T_P_LP_iter |
| `CertifyingDatalogBridge` | CDLGroundAtom ≃ GroundAtom (List↔Fin bridge) |
| `Provenance` | K-relations, T_P_K_LP, semiring homomorphism theorem |
| `PathMapBridge` | Conjunctive queries, evidence counting, monotonicity |
| `RangeRestriction` | `isUnit`, `isRangeRestricted`, unit-KB LHM characterization |
| `Narrowing` | Rules used left to right: narrowing (unification may instantiate the query), rewriting as the narrowing that fixes it, paramodulation into a unit equation, soundness in models; `a ⟶ b`, `a ⟶ c` give `b = c` by paramodulation and no rewriting between `b` and `c`; `f x ⟶ f (g x)` has no reduction order |
| `NarrowingLift` | A rewrite of an instantiated query at a non-variable subterm is an instance of a narrowing by a most general unifier |
| `LinearUnification` | Linear terms (no variable twice): substitution and refilling keep them linear; unifying linear, variable-disjoint equations overlays them, the most general unifier sending left-side variables to linear terms with no shared variable |
| `HypotheticalPropositional` | Propositional hypothetical Datalog: premises under discharged atomic hypotheses; a nested least fixed point decides derivability; weakening, cut, domination and blocking |
-/
