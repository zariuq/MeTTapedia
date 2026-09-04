import Mettapedia.Languages.OpenTheory.TheoryClosure
import Mettapedia.Languages.OpenTheory.AxiomPolicyCanary

/-!
# Canaries for policy-qualified OpenTheory derivability

The one-axiom fixture theory derives its selected axiom but cannot derive a
different axiom that the bare primitive kernel accepts.  The rejection follows
from least-closure provenance, not from a special-case comparison of theorem
conclusions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory
namespace TheoryClosureCanary

open CoreRulesFixtures AxiomPolicyCanary

theorem onlyP_derives_axiomP :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule onlyP) axiomP := by
  exact derives_of_nullary_check onlyP
    (.core (.axiom boolSequentP)) axiomP rfl
    onlyP_allows_axiomP bareKernel_accepts_axiomP

theorem unrestricted_derives_axiomQ :
    Mettapedia.Logic.Derives
      (PolicyPrimitiveRule unrestrictedAxiomPolicy) axiomQ := by
  exact derives_of_nullary_check unrestrictedAxiomPolicy
    (.core (.axiom boolSequentQ)) axiomQ rfl
    (unrestricted_allows_every_request _) bareKernel_accepts_axiomQ

theorem onlyP_disallows_axiomQ_provenance :
    ¬ onlyP.AllowsTheorem axiomQ := by
  intro allowed
  have sequentAllowed : onlyP boolSequentQ :=
    allowed boolSequentQ (by
      simp [axiomQ, Theorem.axiomResult])
  apply onlyP_rejects_axiomQ
  simpa [PrimitiveRequest.InputAxiomsAllowed,
    CoreRequest.InputAxiomsAllowed] using sequentAllowed

/-- Negative control: a theorem accepted as a bare primitive axiom is not a
theorem of an object theory whose policy excludes that axiom. -/
theorem onlyP_does_not_derive_axiomQ :
    ¬ Mettapedia.Logic.Derives (PolicyPrimitiveRule onlyP) axiomQ :=
  underivable_of_disallowed_axioms onlyP axiomQ
    onlyP_disallows_axiomQ_provenance

end TheoryClosureCanary
end Mettapedia.Languages.OpenTheory
