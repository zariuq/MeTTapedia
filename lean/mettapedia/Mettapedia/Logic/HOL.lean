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

Active restart surface for HOL.

This entrypoint intentionally exposes only the substrate we currently trust for a
clean rebuild:

- typed syntax and substitutions,
- const-map transport,
- extensional natural deduction,
- closed-theory provability,
- Lindenbaum machinery,
- prime-extension infrastructure.

Semantic endgames, model bridges, archived routes, and non-core overlays have
been removed from this public surface and are being staged under
`Logic/HOL/_archive/`.
-/
