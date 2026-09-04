import Mettapedia.Languages.OpenTheory.TheoryReplay
import Mettapedia.Languages.OpenTheory.TheoryClosureCanary

/-!
# Canaries for exact replay of a selected OpenTheory theory

The same pinned primitive kernel is replayed under a decidable one-axiom
policy.  A one-node certificate for the selected axiom is accepted; the
structurally identical certificate shape carrying a different axiom request is
rejected.  The checker contains no distinguished HOL or fixture-specific
primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory
namespace TheoryReplayCanary

open Mettapedia.Logic
open CoreRulesFixtures AxiomPolicyCanary

local instance : DecidablePred onlyP := fun sequent =>
  inferInstanceAs (Decidable (sequent = boolSequentP))

abbrev interface : RuleWitness (PolicyPrimitiveRule onlyP) :=
  policyRuleWitness onlyP

def axiomPCertificate : Derivation Theorem interface.W :=
  .node axiomP (.core (.axiom boolSequentP)) 0 (fun position =>
    Fin.elim0 position)

def axiomQCertificate : Derivation Theorem interface.W :=
  .node axiomQ (.core (.axiom boolSequentQ)) 0 (fun position =>
    Fin.elim0 position)

theorem axiomPCertificate_accepted :
    axiomPCertificate.valid interface = true := by
  unfold axiomPCertificate
  simp only [Derivation.valid, List.ofFn_zero, List.all_nil, Bool.and_true]
  change policyRuleIsInstance onlyP (.core (.axiom boolSequentP)) []
      axiomP = true
  apply (policyRuleIsInstance_eq_true_iff onlyP _ [] axiomP).mpr
  exact ⟨rfl, onlyP_allows_axiomP,
    (checkPrimitive_eq_some_iff _ _).mp bareKernel_accepts_axiomP⟩

theorem axiomQCertificate_rejected :
    axiomQCertificate.valid interface = false := by
  unfold axiomQCertificate
  simp only [Derivation.valid, List.ofFn_zero, List.all_nil, Bool.and_true]
  change policyRuleIsInstance onlyP (.core (.axiom boolSequentQ)) []
      axiomQ = false
  cases accepted : policyRuleIsInstance onlyP
      (.core (.axiom boolSequentQ)) [] axiomQ with
  | false => rfl
  | true =>
      have exactStep :=
        (policyRuleIsInstance_eq_true_iff onlyP _ [] axiomQ).mp accepted
      exact (onlyP_rejects_axiomQ exactStep.2.1).elim

/-- Positive control: generic exact replay reconstructs derivability of the
selected object theory. -/
theorem accepted_certificate_is_derivable :
    Derives (PolicyPrimitiveRule onlyP) axiomP :=
  Derivation.valid_sound interface axiomPCertificate
    axiomPCertificate_accepted

/-- Negative control: changing only the axiom request and result is observed
by the same profile-blind replay interface. -/
theorem policy_changes_replay_result :
    axiomPCertificate.valid interface ≠
      axiomQCertificate.valid interface := by
  rw [axiomPCertificate_accepted, axiomQCertificate_rejected]
  decide

end TheoryReplayCanary
end Mettapedia.Languages.OpenTheory
