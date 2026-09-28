import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityGeneration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCoherence

/-!
# Admission of computed reflexivity into an independently checked identity type

The checker may retain different endpoint certificates in a reflexivity proof
and in a subsequent formation of its identity type. Their interpreted endpoint
values, not the syntactic equality of the raw endpoint terms, determine whether
the proof token inhabits that independently formed type. This law applies to
arbitrary computed endpoint terms and to cumulative wrappers on the identity
formation. It does not assert that all accepted endpoint certificates agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Accepted certificates supply all assembly receipts. The equivalence is
not a soundness claim: endpoint disagreement remains a genuine possibility
outside valid contexts. -/
theorem checked_reflexivity_admission_boundary
    (context : Ctx Head n) (A term : Tm Head n) (level : Head)
    (termCode identityCode : Code Head NoConversion n)
    (proofChecked : check R noConversionCheck context (.refl term) (.id A term term)
      (.reflIntro A termCode) = true)
    (identityChecked : check R noConversionCheck context (.id A term term)
      (.head level) identityCode = true) :
    ∃ proof identity leftCode rightCode left right,
      assemble heads constants (.reflIntro A termCode) (.refl term)
        (.id A term term) = some proof ∧
      assemble heads constants identityCode (.id A term term)
        (.head level) = some identity ∧
      check R noConversionCheck context term A leftCode = true ∧
      check R noConversionCheck context term A rightCode = true ∧
      assemble heads constants leftCode term A = some left ∧
      assemble heads constants rightCode term A = some right ∧
      ∀ env, proof.value env ∈ identity.value env ↔
        left.value env = right.value env := by
  obtain ⟨proof, atProof, _⟩ := accepted_assembles heads constants R noConversionCheck
    (.reflIntro A termCode) proofChecked
  obtain ⟨identity, atIdentity, _⟩ := accepted_assembles heads constants R noConversionCheck
    identityCode identityChecked
  obtain ⟨_, _, leftCode, rightCode, _, left, right, _, _, _, _, leftChecked,
    rightChecked, atLeft, atRight, value⟩ :=
      checked_identity_generation heads constants R noConversionCheck identityCode identity
        identityChecked atIdentity
  refine ⟨proof, identity, leftCode, rightCode, left, right, atProof, atIdentity,
    leftChecked, rightChecked, atLeft, atRight, ?_⟩
  intro env
  have proofIsEmpty : proof.value env = ∅ := by
    simp only [assemble, Option.some.injEq] at atProof
    subst proof
    rfl
  rw [value, proofIsEmpty]
  exact (Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding.mem_truthCode _ _).trans
    (and_iff_right rfl)

/-- Any two accepted endpoint certificates of a supported expression give
the same value. Therefore its checked reflexivity proof inhabits an
independently checked identity formation, without choosing a canonical
endpoint certificate or assuming soundness of all accepted derivations. -/
theorem supported_reflexivity_in_independent_identity
    (context : Ctx Head n) (A term : Tm Head n) (level : Head)
    (termCode identityCode : Code Head NoConversion n)
    (supported : ZFSetTypeExpressionInterpretation.supported term = true)
    (proofChecked : check R noConversionCheck context (.refl term) (.id A term term)
      (.reflIntro A termCode) = true)
    (identityChecked : check R noConversionCheck context (.id A term term)
      (.head level) identityCode = true) :
    ∃ proof identity,
      assemble heads constants (.reflIntro A termCode) (.refl term)
        (.id A term term) = some proof ∧
      assemble heads constants identityCode (.id A term term)
        (.head level) = some identity ∧
      ∀ env, proof.value env ∈ identity.value env := by
  obtain ⟨proof, identity, _, _, left, right, atProof, atIdentity, _, _, atLeft,
    atRight, admittedIff⟩ := checked_reflexivity_admission_boundary heads constants R
      context A term level termCode identityCode proofChecked identityChecked
  refine ⟨proof, identity, atProof, atIdentity, ?_⟩
  intro env
  apply (admittedIff env).mpr
  exact congrFun (assemble_supported_values heads constants supported atLeft atRight) env

/-- An arbitrary computed reflexivity argument is admitted by a checked
dependent function precisely when the independently retained endpoint
certificates in that function's identity domain agree. The domain is
extracted from the actual Π-formation certificate; neither the argument nor
the product formation is required to pass result-formation qualification. -/
theorem reflexivity_argument_product_domain_iff
    (context : Ctx Head n) (A term : Tm Head n) (B : Tm Head (n + 1))
    (level domainLevel bodyLevel : Head)
    (termCode formation domainCode : Code Head NoConversion n)
    (bodyCode : Code Head NoConversion (n + 1))
    (proof formed : Meaning.{u} n) (domain : Value.{u} n)
    (proofChecked : check R noConversionCheck context (.refl term) (.id A term term)
      (.reflIntro A termCode) = true)
    (formationChecked : check R noConversionCheck context
      (.pi (.id A term term) B) (.head level) formation = true)
    (parts : formation.piFormation =
      some (domainLevel, bodyLevel, domainCode, bodyCode))
    (atProof : assemble heads constants (.reflIntro A termCode) (.refl term)
      (.id A term term) = some proof)
    (atFormation : assemble heads constants formation
      (.pi (.id A term term) B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain) :
    ∃ leftCode rightCode left right,
      check R noConversionCheck context term A leftCode = true ∧
      check R noConversionCheck context term A rightCode = true ∧
      assemble heads constants leftCode term A = some left ∧
      assemble heads constants rightCode term A = some right ∧
      ∀ env, proof.value env ∈ domain env ↔
        left.value env = right.value env := by
  obtain ⟨_, _, _, _, computed, _, _, domainChecked, _⟩ :=
    formation.piFormation_checked R noConversionCheck formationChecked
  rw [parts] at computed
  cases Option.some.inj computed
  obtain ⟨domainMeaning, _, atDomainCode, _, _, retained⟩ :=
    assemble_piFormation heads constants formation parts atFormation
  rw [atDomain] at retained
  have domainEqual := Option.some.inj retained
  obtain ⟨proofMeaning, identityMeaning, leftCode, rightCode, left, right,
    atProofMeaning, atIdentityMeaning, leftChecked, rightChecked, atLeft, atRight,
    admittedIff⟩ := checked_reflexivity_admission_boundary heads constants R
      context A term domainLevel termCode domainCode proofChecked domainChecked
  rw [atProof] at atProofMeaning
  cases Option.some.inj atProofMeaning
  rw [atDomainCode] at atIdentityMeaning
  cases Option.some.inj atIdentityMeaning
  refine ⟨leftCode, rightCode, left, right, leftChecked, rightChecked, atLeft, atRight, ?_⟩
  intro env
  rw [domainEqual]
  exact admittedIff env

/-- Admission to an independently checked identity domain needs no global
result-formation qualification premise when the endpoint expression is
structurally supported. Every accepted assembly of that endpoint has the
same value, even if the product formation retained different certificates
from the reflexivity proof. This does not cover unsupported beta-redexes. -/
theorem supported_reflexivity_argument_in_product_domain
    (context : Ctx Head n) (A term : Tm Head n) (B : Tm Head (n + 1))
    (level domainLevel bodyLevel : Head)
    (termCode formation domainCode : Code Head NoConversion n)
    (bodyCode : Code Head NoConversion (n + 1))
    (proof formed : Meaning.{u} n) (domain : Value.{u} n)
    (supported : ZFSetTypeExpressionInterpretation.supported term = true)
    (proofChecked : check R noConversionCheck context (.refl term) (.id A term term)
      (.reflIntro A termCode) = true)
    (formationChecked : check R noConversionCheck context
      (.pi (.id A term term) B) (.head level) formation = true)
    (parts : formation.piFormation =
      some (domainLevel, bodyLevel, domainCode, bodyCode))
    (atProof : assemble heads constants (.reflIntro A termCode) (.refl term)
      (.id A term term) = some proof)
    (atFormation : assemble heads constants formation
      (.pi (.id A term term) B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (env : Environment.{u} n) : proof.value env ∈ domain env := by
  obtain ⟨leftCode, rightCode, left, right, _, _, atLeft, atRight, admittedIff⟩ :=
    reflexivity_argument_product_domain_iff heads constants R context A term B level
      domainLevel bodyLevel termCode formation domainCode bodyCode proof formed domain
      proofChecked formationChecked parts atProof atFormation atDomain
  apply (admittedIff env).mpr
  exact congrFun (assemble_supported_values heads constants supported atLeft atRight) env

omit [DecidableEq Head] in
/-- A computed reflexivity term inhabits an independently assembled identity
formation that uses the same endpoint certificate twice. Neither its endpoint
term nor its certificate must be a variable, neutral term, or qualified tree. -/
theorem reflexivity_in_same_endpoint_formation
    (A term : Tm Head n) (level : Head)
    (termCode formation endpointCode : Code Head NoConversion n)
    (proof identity : Meaning.{u} n)
    (atProof : assemble heads constants (.reflIntro A termCode) (.refl term)
      (.id A term term) = some proof)
    (atIdentity : assemble heads constants (.idForm level formation endpointCode endpointCode)
      (.id A term term) (.head level) = some identity) :
    ∀ env, proof.value env ∈ identity.value env := by
  cases atEndpoint : assemble heads constants endpointCode term A with
  | none => simp [assemble, atEndpoint] at atIdentity
  | some endpoint =>
    simp [assemble, atEndpoint] at atIdentity atProof
    subst proof
    subst identity
    intro env
    change (∅ : ZFSet.{u}) ∈
      Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding.truthCode True
    exact (Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding.mem_truthCode True ∅).mpr
      ⟨rfl, True.intro⟩

#print axioms checked_reflexivity_admission_boundary
#print axioms supported_reflexivity_in_independent_identity
#print axioms reflexivity_argument_product_domain_iff
#print axioms supported_reflexivity_argument_in_product_domain
#print axioms reflexivity_in_same_endpoint_formation

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
