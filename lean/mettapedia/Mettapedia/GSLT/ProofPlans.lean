import Mettapedia.GSLT.ProofPlans.Plan
import Mettapedia.GSLT.ProofPlans.Contexts
import Mettapedia.GSLT.ProofPlans.Fixture
import Mettapedia.GSLT.ProofPlans.Derivations
import Mettapedia.GSLT.ProofPlans.Execution
import Mettapedia.GSLT.ProofPlans.Search
import Mettapedia.GSLT.ProofPlans.Composition
import Mettapedia.GSLT.ProofPlans.Transforms
import Mettapedia.GSLT.ProofPlans.Generalization
import Mettapedia.GSLT.ProofPlans.Evidence
import Mettapedia.GSLT.ProofPlans.WorkPlans

/-!
# Proof plans as partial programs

A proof plan is a derivation with holes: its holes are its obligations, and
its completion space is the set of complete derivations obtained by
discharging them.  For a validated proof definition, plans are
`OpenDerivation`s, the operations of the definition's derivation clone.

* `ProofPlans.Plan`: plans of a multisorted clone; completion spaces,
  refinement, the generalization order, the most general and the closed plans,
  clone algebras (fill-and-resume) and truth assignments (soundness).
* `ProofPlans.Contexts`: injectivity of the wire erasure of open derivations;
  raw closed proofs as raw open proofs.
* `ProofPlans.Fixture`: a validated kernel, a method library with its
  elaboration, an unsound library, and a two-bit calculus, with independent
  truth assignments.
* `ProofPlans.Derivations`: completions are discharges; plan soundness for
  untrusted artifacts, for semantics and through elaboration.
* `ProofPlans.Execution`: incremental execution is fill-and-resume, with the
  recorded context, purity and termination each shown necessary; costs.
* `ProofPlans.Search`: budgeted backward-chaining plan search with authority
  outcomes; exhaustion is incomplete, never refuted.
* `ProofPlans.Composition`: plan networks; joint completion is a global
  section; pairwise-compatible plans that fail jointly; holonomy.
* `ProofPlans.Transforms`: anti-unification, abduction, blending and bypass,
  with what each preserves and a naive variant that loses it.
* `ProofPlans.Generalization`: least general generalization, sharing one
  obligation across repeated erasure pairs, and its instance of the linear
  anti-unification.
* `ProofPlans.Evidence`: evidence records as a readout; ranking without
  substitution; provenance and double counting.
* `ProofPlans.WorkPlans`: plans whose steps act; what receipts must provide.
-/
