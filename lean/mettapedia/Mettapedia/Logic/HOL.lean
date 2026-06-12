import Mettapedia.Logic.HOL.Syntax.Type
import Mettapedia.Logic.HOL.Syntax.Term
import Mettapedia.Logic.HOL.Syntax.Subst
import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Syntax.ConstMap
import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.Lindenbaum
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.LindenbaumSet
import Mettapedia.Logic.HOL.PrimeHenkinExtension
import Mettapedia.Logic.HOL.Syntax.FreshConst
import Mettapedia.Logic.HOL.CanonicalQuantifierBridges
import Mettapedia.Logic.HOL.WitnessedExtension
import Mettapedia.Logic.HOL.WitnessedSaturation
import Mettapedia.Logic.HOL.MaximalConsistent
import Mettapedia.Logic.HOL.WitnessedWorld
import Mettapedia.Logic.HOL.WorldEquality
import Mettapedia.Logic.HOL.ClassicalExcludedMiddle
import Mettapedia.Logic.HOL.ClassicalWorld
import Mettapedia.Logic.HOL.TermModel.Domain
import Mettapedia.Logic.HOL.TermModel.Truth
import Mettapedia.Logic.HOL.TermModel.Realize
import Mettapedia.Logic.HOL.TermModel.Denote
import Mettapedia.Logic.HOL.TermModel.PreModelWrapper
import Mettapedia.Logic.HOL.TermModel.Fundamental
import Mettapedia.Logic.HOL.TermModel.HenkinCompleteness

/-!
# Higher-Order Logic Core

Public surface for HOL: the trusted substrate plus the completed **classical Henkin
completeness** development.

Substrate:
- typed syntax and substitutions, const-map transport,
- extensional natural deduction, closed-theory provability,
- Lindenbaum machinery, prime-extension infrastructure.

Completeness (Henkin 1950 for the theory of types — sorry-free, axiom-clean):
- the fresh-constant generalization `provable_all_intro_fresh` and the Henkin
  witnessing/saturation chain (`witnessLimit_consistent`, `exists_witnessAxiom`),
- the Lindenbaum maximal extension and the classical canonical world
  (`exists_classical_world`, including the `all_counterexample` field),
- the canonical Henkin **general** term model (`TermModel/`), the fundamental lemma,
  and `models_iff_mem`,
- the headline `TermModel.HenkinCompleteness.henkin_satisfiable`: a consistent
  *witnessed + excluded-middle* theory has a Henkin general model satisfying it.

Legacy `WorldModelCompleteness.lean` (hypothesis-parameterised) is retained but is not
the active completeness surface.
-/
