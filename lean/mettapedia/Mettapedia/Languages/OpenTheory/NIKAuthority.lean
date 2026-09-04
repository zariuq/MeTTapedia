import Mettapedia.Languages.OpenTheory.TheoryReplay
import Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority

/-!
# NIK authority for policy-qualified OpenTheory closure

For each explicit axiom policy, the pinned OpenTheory primitive rules form a
qualified finitary rule system.  Its least closure is the proof scope, while
the independently proved semantic predicate at this layer is exactly axiom
provenance authorization.

This supplies a concrete NIK authority object and proof-fibre equivalence.  It
does not call an unspecified policy “HOL”, and authorization is not claimed to
be model-theoretic truth.  A selected HOL object theory owes an explicit axiom
bundle and a separate sound interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.NIKAuthority

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority

/-- The pinned primitive closure qualified by one explicit axiom policy.
Authorized provenance is the semantic invariant proved independently of
replay. -/
def ruleSystem (policy : AxiomPolicy) [DecidablePred policy] :
    QualifiedRuleSystem Theorem where
  rules := PolicyPrimitiveRule policy
  witness := policyRuleWitness policy
  Meaning := policy.AllowsTheorem
  rules_sound := by
    intro premises conclusion rule _premisesAllowed
    exact rule.outputAxiomsAllowed policy

/-- NIK theory family whose scope is least policy-qualified derivability. -/
abbrev theory (policy : AxiomPolicy) [DecidablePred policy] :=
  (ruleSystem policy).theory

/-- Exact finite replay contract for policy-qualified OpenTheory. -/
abbrev contract (policy : AxiomPolicy) [DecidablePred policy] :=
  (ruleSystem policy).contract

/-- The native derivation-tree discipline retained by the NIK boundary. -/
abbrev evidenceDiscipline (policy : AxiomPolicy) [DecidablePred policy] :=
  (ruleSystem policy).evidenceDiscipline

/-- Replay and native proof inhabitation have equivalent accepted fibres. -/
abbrev proofCarryingAuthority
    (policy : AxiomPolicy) [DecidablePred policy] :=
  (ruleSystem policy).proofCarryingAuthority

/-- Every accepted certificate concludes a theorem whose complete axiom
provenance is authorized by the selected policy. -/
theorem accepted_has_authorized_axioms
    (policy : AxiomPolicy) [DecidablePred policy]
    (claim : Theorem)
    (certificate : Derivation Theorem (policyRuleWitness policy).W)
    (accepted :
      ((contract policy).checker ()).check claim certificate = true) :
    policy.AllowsTheorem claim := by
  exact (ruleSystem policy).accepted_meaning claim certificate accepted

/-- A theorem outside the selected provenance policy has no accepted replay
certificate. -/
theorem unauthorized_has_no_certificate
    (policy : AxiomPolicy) [DecidablePred policy]
    (claim : Theorem) (unauthorized : ¬ policy.AllowsTheorem claim) :
    ¬ ∃ certificate : Derivation Theorem (policyRuleWitness policy).W,
      ((contract policy).checker ()).check claim certificate = true := by
  rintro ⟨certificate, accepted⟩
  exact unauthorized
    (accepted_has_authorized_axioms policy claim certificate accepted)

/-- The NIK scope remains exactly the structural derivation fibre; no semantic
witness is substituted for a replay certificate. -/
theorem scope_iff_structural_derivation
    (policy : AxiomPolicy) [DecidablePred policy] (claim : Theorem) :
    (theory policy).Scope () claim ↔
      ∃ certificate : Derivation Theorem (policyRuleWitness policy).W,
        certificate.valid (policyRuleWitness policy) = true ∧
          certificate.concl = claim := by
  exact (ruleSystem policy).scope_iff_structural_derivation claim

end Mettapedia.Languages.OpenTheory.NIKAuthority
