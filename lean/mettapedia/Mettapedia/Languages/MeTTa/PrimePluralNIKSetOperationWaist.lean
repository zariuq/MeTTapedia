import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
import Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist
import Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority

/-!
# Selected set operations in the plural Prime NIK waist

The current plural Prime waist and the externally interpreted Megalodon
empty/union/powerset authority coexist as a conservative coproduct.  The new
node is deliberately a selected operation fragment rather than an alias for
the retained set core or a claim to the full HOTG preamble.

Its native scope consists of five ordinary Mathdata proofs.  Its meaning is
validity in every extensional membership model satisfying the exact selected
operation laws.  Coproduct tags retain the different claim and certificate
fibres, while exact inclusion preserves both checker replay and external
meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u v

private abbrev priorTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.theory.{u, v}

private abbrev priorContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.contract.{u, v}

private abbrev operationTheory :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.theory

private abbrev operationContract :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.contract

/-- The established Prime authority graph or the selected set-operation
authority. -/
abbrev Kind := Sum
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.Kind Unit

def atomlessBooleanKind : Kind :=
  .inl
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.atomlessBooleanKind

def setOperationKind : Kind := .inr ()

def theory := Coproduct.theory priorTheory.{u, v} operationTheory

def contract :=
  Coproduct.contract priorTheory.{u, v} operationTheory priorContract.{u, v}
    operationContract

def priorInclusion :=
  Coproduct.leftInclusion priorTheory.{u, v} operationTheory
    priorContract.{u, v} operationContract

def operationInclusion :=
  Coproduct.rightInclusion priorTheory.{u, v} operationTheory
    priorContract.{u, v} operationContract

theorem priorInclusion_conservative :
    priorInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative priorTheory.{u, v} operationTheory
    priorContract.{u, v} operationContract

theorem operationInclusion_conservative :
    operationInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.rightInclusion_conservative priorTheory.{u, v} operationTheory
    priorContract.{u, v} operationContract

private theorem operationIdentity_conservative :
    (TheoryTranslation.identity operationTheory).Conservative where
  scope_reflecting := by
    intro kind formula inScope
    exact inScope
  meaning_reflecting := by
    intro kind formula meaningful
    exact meaningful

/-! ## Exact host irrelevance -/

theorem operation_scope_is_host_irrelevant
    (formula : operationTheory.Claim ()) :
    operationTheory.Scope () formula <->
      theory.{u, v}.Scope setOperationKind formula :=
  HostIrrelevance.scope_iff
    (TheoryTranslation.identity operationTheory)
    operationInclusion.{u, v}.toTheoryTranslation
    operationIdentity_conservative operationInclusion_conservative.{u, v}
    () formula

theorem operation_meaning_is_host_irrelevant
    (formula : operationTheory.Claim ()) :
    operationTheory.Meaning () formula <->
      theory.{u, v}.Meaning setOperationKind formula :=
  HostIrrelevance.meaning_iff
    (TheoryTranslation.identity operationTheory)
    operationInclusion.{u, v}.toTheoryTranslation
    operationIdentity_conservative operationInclusion_conservative.{u, v}
    () formula

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority

noncomputable section

local instance : DecidableEq Kind := Classical.decEq Kind

theorem unionIntroduction_replays :
    (contract.{u, v}.checker setOperationKind).check
      unionIntroFormula AxiomTag.unionIntro.proof = true :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem powerElimination_replays :
    (contract.{u, v}.checker setOperationKind).check
      powerElimFormula AxiomTag.powerElim.proof = true :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.powerElim_replays

theorem powerIntroduction_has_external_meaning :
    theory.{u, v}.Meaning setOperationKind powerIntroFormula :=
  powerIntro_valid

theorem universalMembership_not_meaning :
    Not (theory.{u, v}.Meaning setOperationKind
      universalMembership) :=
  universalMembership_not_valid

/-- External validity remains broader than the five selected native rules. -/
theorem valid_identity_not_in_native_scope :
    theory.{u, v}.Meaning setOperationKind identityFormula /\
      Not (theory.{u, v}.Scope setOperationKind identityFormula) :=
  ⟨identity_valid, identity_not_covered⟩

/-- An operation certificate cannot cross the outer authority tag into the
retained atomless node. -/
theorem operation_certificate_rejected_at_atomless_kind :
    contract.{u, v}.toAuthorityFamily.packedChecker.check
      ⟨atomlessBooleanKind,
        Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence⟩
      ⟨setOperationKind, AxiomTag.unionIntro.proof⟩ = false := by
  exact AuthorityFamily.packedChecker_rejects_wrongKind
    (family := contract.{u, v}.toAuthorityFamily)
    (claimKind := atomlessBooleanKind)
    (certificateKind := setOperationKind)
    (by simp [atomlessBooleanKind, setOperationKind])
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence
    AxiomTag.unionIntro.proof

end

end Canary

#print axioms priorInclusion_conservative
#print axioms operationInclusion_conservative
#print axioms operation_scope_is_host_irrelevant
#print axioms operation_meaning_is_host_irrelevant
#print axioms Canary.unionIntroduction_replays
#print axioms Canary.powerElimination_replays
#print axioms Canary.powerIntroduction_has_external_meaning
#print axioms Canary.universalMembership_not_meaning
#print axioms Canary.valid_identity_not_in_native_scope
#print axioms Canary.operation_certificate_rejected_at_atomless_kind

end Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist
