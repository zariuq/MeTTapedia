import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicenceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchValueStates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricOpenControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OrderedMatchCompatibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OrderedFinite

/-!
# First-order CMR solver licences and symmetric match identity

The solver decision procedure characterizes universal entailment over all
substitutions. Symmetric match classes retain whole-rule local-variable sharing,
pattern/occurrence incidence and take/read polarity. Actual jointly fresh bags
are compared through their residual models, source interfaces and labelled
result states. Ordered-key and named-origin readings remain separate.

The first-order profile uses finite occurs-checked terms, one occurrence-bag
store, ambient programs and guards after own tells. Guard timing, set stores,
world-indexed knowledge and scheduling are not selected by this package.
Native runtime refinement and cost bounds are separate obligations.
-/
