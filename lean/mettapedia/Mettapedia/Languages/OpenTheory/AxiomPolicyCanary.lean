import Mettapedia.Languages.OpenTheory.AxiomPolicy
import Mettapedia.Languages.OpenTheory.CoreRulesFixtures

/-!
# Canaries for the OpenTheory kernel/object-theory boundary

The bare primitive kernel accepts two well-typed axiom requests.  A policy
selecting only one of their sequents admits exactly that request.  This is a
concrete discriminator between a pinned inference kernel and an object theory
built over it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory
namespace AxiomPolicyCanary

open CoreRulesFixtures

/-- A deliberately small object theory admitting exactly one fixture axiom. -/
def onlyP : AxiomPolicy := fun sequent => sequent = boolSequentP

theorem bareKernel_accepts_axiomP :
    checkPrimitive (.core (.axiom boolSequentP)) = some axiomP := by
  rw [checkPrimitive, checkCore]
  apply (checkAxiom_eq_some_iff boolSequentP axiomP).mpr
  exact ⟨boolSequentP_isBool,
    (theorem_axiomResult_eq_iff_hasParts
      boolSequentP boolSequentP_isBool axiomP).mp rfl⟩

theorem bareKernel_accepts_axiomQ :
    checkPrimitive (.core (.axiom boolSequentQ)) = some axiomQ := by
  rw [checkPrimitive, checkCore]
  apply (checkAxiom_eq_some_iff boolSequentQ axiomQ).mpr
  exact ⟨boolSequentQ_isBool,
    (theorem_axiomResult_eq_iff_hasParts
      boolSequentQ boolSequentQ_isBool axiomQ).mp rfl⟩

theorem onlyP_allows_axiomP :
    (PrimitiveRequest.core (.axiom boolSequentP)).InputAxiomsAllowed onlyP := by
  simp [PrimitiveRequest.InputAxiomsAllowed,
    CoreRequest.InputAxiomsAllowed, onlyP]

theorem onlyP_rejects_axiomQ :
    ¬ (PrimitiveRequest.core (.axiom boolSequentQ)).InputAxiomsAllowed
      onlyP := by
  simp [PrimitiveRequest.InputAxiomsAllowed,
    CoreRequest.InputAxiomsAllowed, onlyP, boolSequentP, boolSequentQ,
    CoreRulesFixtures.p, CoreRulesFixtures.q, SequentExamples.boolVariable,
    Name.global]

/-- Positive control: policy-qualified execution produces authorized
provenance. -/
theorem axiomP_output_authorized : onlyP.AllowsTheorem axiomP :=
  checkPrimitive_outputAxiomsAllowed onlyP _ _ onlyP_allows_axiomP
    bareKernel_accepts_axiomP

/-- Negative control: bare kernel acceptance does not imply object-theory
admission. -/
theorem bare_acceptance_does_not_fix_object_theory :
    checkPrimitive (.core (.axiom boolSequentQ)) = some axiomQ ∧
      ¬ (PrimitiveRequest.core (.axiom boolSequentQ)).InputAxiomsAllowed
        onlyP :=
  ⟨bareKernel_accepts_axiomQ, onlyP_rejects_axiomQ⟩

end AxiomPolicyCanary
end Mettapedia.Languages.OpenTheory
