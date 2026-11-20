import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderAskLicence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreInvariance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplineControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreAliasControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreGrowthControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStorePathControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedPathControls

/-!
# Ask timing, normalized set steps and least completed outcomes

The contracts are separate from the existing occurrence calculus. Positive
propagation requires ground input and range restriction; finite termination
requires a finite closed carrier. Unique admission additionally requires
determinate match classes. Counterexamples retain the omitted distinctions.
Quantified commits at the ask timing are named separately from restricting
after-tells commits; they agree on the tell-free propagation fragment.
-/
