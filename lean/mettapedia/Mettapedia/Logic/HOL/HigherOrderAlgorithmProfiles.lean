import Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT

/-!
# Higher-order algorithm profiles over one TH0 interchange boundary

TH0 is a logic and an interchange language, not one search algorithm.  A
checked TH0 artifact may be consumed by substitution, unification, uniform
proof search, lambda-superposition, proof planning, inductive learning, model
finding, or an infinitary extension.  Those consumers share a small typed
frontier and then require genuinely different services.

This module makes that choice map explicit.  The finite sets below are a
dependency ledger: membership records a named obligation, but does not claim
that an implementation satisfies the obligation.  Semantic authority remains
with an independent checker, while candidate generation remains replaceable.

The resulting order has two useful features.  First, the implemented
syntactic-substitution service is proved strictly weaker than beta-eta
unification, which is itself strictly weaker than the declared
lambda-superposition profile.  Second, uniform proofs, proof planning, higher-
order ILP, model finding, and infinitary proof search are not arranged in one
misleading linear hierarchy: their profiles are provably incomparable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HigherOrderAlgorithmProfiles

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic.ProofProducingSearch
open Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary

/-! ## Artifact guarantees and algorithm capabilities -/

/-- Named capabilities at the boundary between an elaborated TH0 artifact and
one of its possible reasoning consumers.  This is intentionally more granular
than the earlier substitution-versus-superposition ledger. -/
inductive Capability where
  | typedLambdaSyntax
  | scopedBinders
  | declaredSignature
  | canonicalWire
  | captureAvoidingSubstitution
  | simultaneousSubstitution
  | syntacticEquality
  | betaEtaConversion
  | higherOrderPatternUnification
  | generalHigherOrderUnification
  | extensionalityPolicy
  | choicePolicy
  | henkinSemanticPolicy
  | higherOrderClausification
  | orderingAndEligibility
  | focusedUniformRules
  | hypotheticalGoals
  | proofMethods
  | ripplingAndCritics
  | hypothesisSynthesis
  | labelledExamples
  | hypothesisScoring
  | modelEvaluation
  | finiteDomainEnumeration
  | countermodelCertificates
  | indexedPremises
  | countableConnectives
  | productivityOrLiveness
  | independentReplay
  | fairAnytimeSearch
deriving Repr, DecidableEq

/-- What the portable, elaborated TH0 artifact itself supplies.  In particular,
it does not silently include beta-eta conversion or an inference calculus. -/
def portableTH0Guarantees : Finset Capability :=
  { .typedLambdaSyntax, .scopedBinders, .declaredSignature, .canonicalWire }

/-- Additional guarantees supplied by the checked simultaneous-substitution
service. -/
def substitutionServiceGuarantees : Finset Capability :=
  portableTH0Guarantees ∪
    { .captureAvoidingSubstitution, .simultaneousSubstitution,
      .syntacticEquality, .independentReplay }

/-- Distinct tasks for which one may build a TH0-aware consumer. -/
inductive ReasoningRole where
  | syntacticSubstitution
  | betaEtaUnification
  | uniformProofSearch
  | lambdaSuperposition
  | proofPlanning
  | higherOrderInductiveLearning
  | finiteModelFinding
  | infinitaryProofSearch
deriving Repr, DecidableEq

/-- Declared obligations of each reasoning role.  These are requirements for
honest use of the role name, not an implementation certificate. -/
def requirements : ReasoningRole → Finset Capability
  | .syntacticSubstitution => substitutionServiceGuarantees
  | .betaEtaUnification => substitutionServiceGuarantees ∪
      { .betaEtaConversion, .higherOrderPatternUnification,
        .generalHigherOrderUnification, .fairAnytimeSearch }
  | .uniformProofSearch => portableTH0Guarantees ∪
      { .captureAvoidingSubstitution, .betaEtaConversion,
        .higherOrderPatternUnification, .focusedUniformRules,
        .hypotheticalGoals, .independentReplay, .fairAnytimeSearch }
  | .lambdaSuperposition => substitutionServiceGuarantees ∪
      { .betaEtaConversion, .higherOrderPatternUnification,
        .generalHigherOrderUnification, .extensionalityPolicy, .choicePolicy,
        .higherOrderClausification, .orderingAndEligibility,
        .fairAnytimeSearch }
  | .proofPlanning => portableTH0Guarantees ∪
      { .captureAvoidingSubstitution, .betaEtaConversion,
        .higherOrderPatternUnification, .proofMethods,
        .ripplingAndCritics, .hypothesisSynthesis,
        .independentReplay, .fairAnytimeSearch }
  | .higherOrderInductiveLearning => portableTH0Guarantees ∪
      { .captureAvoidingSubstitution, .betaEtaConversion,
        .higherOrderPatternUnification, .hypothesisSynthesis,
        .labelledExamples, .hypothesisScoring,
        .independentReplay, .fairAnytimeSearch }
  | .finiteModelFinding => portableTH0Guarantees ∪
      { .betaEtaConversion, .extensionalityPolicy, .choicePolicy,
        .henkinSemanticPolicy, .modelEvaluation, .finiteDomainEnumeration,
        .countermodelCertificates, .independentReplay, .fairAnytimeSearch }
  | .infinitaryProofSearch => portableTH0Guarantees ∪
      { .captureAvoidingSubstitution, .betaEtaConversion,
        .higherOrderPatternUnification, .indexedPremises,
        .countableConnectives, .productivityOrLiveness,
        .independentReplay, .fairAnytimeSearch }

/-- Neither requirement set refines the other. -/
def Incomparable (first second : Finset Capability) : Prop :=
  (∃ capability, capability ∈ first ∧ capability ∉ second) ∧
    (∃ capability, capability ∈ second ∧ capability ∉ first)

theorem Incomparable.not_subset {first second : Finset Capability}
    (separated : Incomparable first second) :
    ¬ first ⊆ second ∧ ¬ second ⊆ first := by
  rcases separated with
    ⟨⟨leftOnly, leftMember, leftAbsent⟩,
      ⟨rightOnly, rightMember, rightAbsent⟩⟩
  constructor
  · intro subset
    exact leftAbsent (subset leftMember)
  · intro subset
    exact rightAbsent (subset rightMember)

/-! ## The proved choice map -/

theorem every_role_consumes_the_portable_core (role : ReasoningRole) :
    portableTH0Guarantees ⊆ requirements role := by
  cases role <;> decide

theorem every_role_requires_independent_replay (role : ReasoningRole) :
    .independentReplay ∈ requirements role := by
  cases role <;> decide

theorem syntactic_substitution_strictly_below_betaEta_unification :
    requirements .syntacticSubstitution ⊂
      requirements .betaEtaUnification := by
  decide

theorem betaEta_unification_strictly_below_lambda_superposition :
    requirements .betaEtaUnification ⊂
      requirements .lambdaSuperposition := by
  decide

theorem uniform_proofs_and_lambda_superposition_are_incomparable :
    Incomparable (requirements .uniformProofSearch)
      (requirements .lambdaSuperposition) := by
  exact ⟨⟨.focusedUniformRules, by decide, by decide⟩,
    ⟨.higherOrderClausification, by decide, by decide⟩⟩

theorem proof_planning_and_lambda_superposition_are_incomparable :
    Incomparable (requirements .proofPlanning)
      (requirements .lambdaSuperposition) := by
  exact ⟨⟨.proofMethods, by decide, by decide⟩,
    ⟨.orderingAndEligibility, by decide, by decide⟩⟩

theorem higherOrder_ILP_and_lambda_superposition_are_incomparable :
    Incomparable (requirements .higherOrderInductiveLearning)
      (requirements .lambdaSuperposition) := by
  exact ⟨⟨.labelledExamples, by decide, by decide⟩,
    ⟨.higherOrderClausification, by decide, by decide⟩⟩

theorem finite_models_and_lambda_superposition_are_incomparable :
    Incomparable (requirements .finiteModelFinding)
      (requirements .lambdaSuperposition) := by
  exact ⟨⟨.finiteDomainEnumeration, by decide, by decide⟩,
    ⟨.generalHigherOrderUnification, by decide, by decide⟩⟩

theorem infinitary_and_finitary_superposition_are_incomparable :
    Incomparable (requirements .infinitaryProofSearch)
      (requirements .lambdaSuperposition) := by
  exact ⟨⟨.indexedPremises, by decide, by decide⟩,
    ⟨.orderingAndEligibility, by decide, by decide⟩⟩

theorem learning_and_model_finding_are_incomparable :
    Incomparable (requirements .higherOrderInductiveLearning)
      (requirements .finiteModelFinding) := by
  exact ⟨⟨.hypothesisSynthesis, by decide, by decide⟩,
    ⟨.modelEvaluation, by decide, by decide⟩⟩

/-! ## One common proof-producing boundary -/

universe uId uClaim uCertificate uOrigin

/-- Any algorithm role may enumerate candidates, but only an independent
semantic authority may accept them.  The role tag states intent; it does not
turn the requirements ledger into a proof that the producer implements every
named capability. -/
structure CheckedCandidateSource
    {AuthorityId : Type uId} {Claim : Type uClaim}
    (authority : SemanticAuthority.{uId, uClaim, uCertificate}
      AuthorityId Claim)
    (Origin : Type uOrigin) where
  role : ReasoningRole
  producer : StagedProducer authority Origin

namespace CheckedCandidateSource

variable {AuthorityId : Type uId} {Claim : Type uClaim}
variable {authority : SemanticAuthority.{uId, uClaim, uCertificate}
  AuthorityId Claim}
variable {Origin : Type uOrigin}

/-- The role of the candidate generator cannot affect accepted meaning. -/
theorem accepted_sound
    (source : CheckedCandidateSource authority Origin)
    {stage : Nat} (accepted : source.producer.AcceptedAt stage) :
    authority.Meaning accepted.proposal.claim :=
  accepted.sound

/-- Eventual success is sound but remains only the positive half of a decision
procedure. -/
theorem eventual_acceptance_sound
    (source : CheckedCandidateSource authority Origin) {claim : Claim}
    (accepted : source.producer.EventuallyAccepts claim) :
    authority.Meaning claim :=
  accepted.sound

end CheckedCandidateSource

/-! ## The implemented syntactic service occupies exactly one node -/

namespace Canary

open Mettapedia.Logic.HOL.TH0SyntacticUnifierService
open Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT

/-- The existing producer is classified as syntactic substitution/unification,
not as a lambda-superposition prover. -/
def syntacticSource :
    CheckedCandidateSource authority
      Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.SearchOrigin where
  role := .syntacticSubstitution
  producer :=
    Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.producer

theorem syntacticSource_role :
    syntacticSource.role = .syntacticSubstitution :=
  rfl

/-- Its accepted certificate already has the proof-relevant operational cospan
proved at the GSLT boundary. -/
theorem accepted_syntactic_certificate_has_operational_cospan :
    ∃ unifier : Unifier
        Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.baseProblem,
      (theory
          Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.baseProblem.type.decode).Step
          (UnifierOps.leftState unifier) (UnifierOps.apex unifier) ∧
        (theory
          Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.baseProblem.type.decode).Step
          (UnifierOps.rightState unifier) (UnifierOps.apex unifier) :=
  Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT.Canary.accepted_packet_has_cospan

/-- Positive and negative control: the service performs checked substitution,
while the beta-redex example lies strictly outside literal syntactic
unification even though one checked beta step reaches the right-hand side. -/
theorem implemented_boundary_is_strict :
    check Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.baseProblem
        Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.certificateA =
      true ∧
      check Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.betaProblem
          Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.identityCertificate =
        false ∧
      betaResult? []
          Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.individual
          Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.individual
          (encodeTerm
            Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.closedA)
          (encodeTerm
            Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.identityBody) =
        some (encodeTerm
          Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.closedA) :=
  ⟨Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.certificateA_accepted,
    Mettapedia.Logic.HOL.TH0SyntacticUnifierService.Canary.substitution_is_not_betaEta_unification⟩

end Canary

/-! ## Audited theorem crowns -/

#print axioms every_role_consumes_the_portable_core
#print axioms every_role_requires_independent_replay
#print axioms Incomparable.not_subset
#print axioms syntactic_substitution_strictly_below_betaEta_unification
#print axioms betaEta_unification_strictly_below_lambda_superposition
#print axioms uniform_proofs_and_lambda_superposition_are_incomparable
#print axioms proof_planning_and_lambda_superposition_are_incomparable
#print axioms higherOrder_ILP_and_lambda_superposition_are_incomparable
#print axioms finite_models_and_lambda_superposition_are_incomparable
#print axioms infinitary_and_finitary_superposition_are_incomparable
#print axioms learning_and_model_finding_are_incomparable
#print axioms CheckedCandidateSource.accepted_sound
#print axioms CheckedCandidateSource.eventual_acceptance_sound
#print axioms Canary.accepted_syntactic_certificate_has_operational_cospan
#print axioms Canary.implemented_boundary_is_strict

end Mettapedia.Logic.HOL.HigherOrderAlgorithmProfiles
