import Mettapedia.Languages.OpenTheory.NIKAuthority
import Mettapedia.Languages.OpenTheory.TheoryReplayCanary

/-!
# Controls for the policy-qualified OpenTheory NIK authority

One policy-selected axiom crosses the generic NIK replay boundary.  A theorem
tagged by the rejected axiom has no certificate in the same authority object.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.NIKAuthorityCanary

open Mettapedia.Languages.OpenTheory.NIKAuthority
open Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
open Mettapedia.Languages.OpenTheory.TheoryReplayCanary
open Mettapedia.Languages.OpenTheory.TheoryClosureCanary
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures

local instance : DecidablePred onlyP := fun sequent =>
  inferInstanceAs (Decidable (sequent = boolSequentP))

/-- The concrete positive replay certificate inhabits the NIK contract. -/
theorem selected_axiom_accepted :
    ((contract onlyP).checker ()).check axiomP axiomPCertificate = true :=
  by
    change
      (axiomPCertificate.valid (policyRuleWitness onlyP) &&
        decide (axiomPCertificate.concl = axiomP)) = true
    rw [Bool.and_eq_true]
    constructor
    · unfold axiomPCertificate
      simp only [Mettapedia.Logic.Derivation.valid, List.ofFn_zero,
        List.all_nil, Bool.and_true]
      change policyRuleIsInstance onlyP
        (.core (.axiom boolSequentP)) [] axiomP = true
      apply (policyRuleIsInstance_eq_true_iff onlyP _ [] axiomP).mpr
      exact ⟨rfl, onlyP_allows_axiomP,
        (checkPrimitive_eq_some_iff _ _).mp bareKernel_accepts_axiomP⟩
    · simp only [axiomPCertificate,
        Mettapedia.Logic.Derivation.concl, decide_true]

/-- The accepted theorem projects to the independent authorization
predicate. -/
theorem selected_axiom_authorized : onlyP.AllowsTheorem axiomP :=
  accepted_has_authorized_axioms onlyP axiomP axiomPCertificate
    selected_axiom_accepted

/-- The same NIK authority rejects the disallowed axiom request. -/
theorem rejected_axiom_certificate_rejected :
    ((contract onlyP).checker ()).check axiomQ axiomQCertificate = false :=
  by
    change
      (axiomQCertificate.valid (policyRuleWitness onlyP) &&
        decide (axiomQCertificate.concl = axiomQ)) = false
    have invalid :
        axiomQCertificate.valid (policyRuleWitness onlyP) = false := by
      unfold axiomQCertificate
      simp only [Mettapedia.Logic.Derivation.valid, List.ofFn_zero,
        List.all_nil, Bool.and_true]
      change policyRuleIsInstance onlyP
        (.core (.axiom boolSequentQ)) [] axiomQ = false
      cases accepted : policyRuleIsInstance onlyP
          (.core (.axiom boolSequentQ)) [] axiomQ with
      | false => rfl
      | true =>
          have exactStep :=
            (policyRuleIsInstance_eq_true_iff onlyP _ [] axiomQ).mp accepted
          exact (onlyP_rejects_axiomQ exactStep.2.1).elim
    rw [invalid]
    rfl

/-- More strongly, no alternate certificate can establish the theorem whose
axiom provenance violates the selected policy. -/
theorem rejected_axiom_has_no_certificate :
    ¬ ∃ certificate,
      ((contract onlyP).checker ()).check axiomQ certificate = true :=
  unauthorized_has_no_certificate onlyP axiomQ
    onlyP_disallows_axiomQ_provenance

end Mettapedia.Languages.OpenTheory.NIKAuthorityCanary
