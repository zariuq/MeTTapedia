import Mettapedia.Computability.StreamingComposition
import Mettapedia.Languages.Chaitin.Frontend
import Mettapedia.Languages.Chaitin.RuntimeControls
import Mettapedia.Languages.Chaitin.EnvironmentLaws
import Mettapedia.Languages.Chaitin.ExpressionLaws
import Mettapedia.Languages.Chaitin.ProgramInput
import Mettapedia.Languages.Chaitin.ProgramMass
import Mettapedia.Languages.Chaitin.RowSearch
import Mettapedia.Languages.Chaitin.TransitionEvaluation
import Mettapedia.Languages.Chaitin.GSLT.Controls
import Mettapedia.Languages.Chaitin.GSLT.CodePreparation

/-!
# Historical Chaitin Lisp

The 1997 values, readers, and streaming evaluator share compositional pure
semantics. The ordinary recursive table interpreter preserves and reflects
termination and final configurations. A validated evaluator LanguageDef
generates its pure control steps, with explicit dynamic environments and
continuations. The existing finite universal table runs through those steps;
input preparation is primitive recursive and successful return is undecidable
under the framework's structural term numbering.
-/
