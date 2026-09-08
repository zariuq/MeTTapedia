import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory

/-!
# Derivability shadows and semantic qualification

An exact authority contains two logically distinct predicates: native proof
scope and independently authored meaning.  This module isolates their seam.

The derivability shadow of an authority retains its kinds, signatures, claims,
proof scope, certificates, and checker, but uses proof scope itself as its only
meaning predicate.  This operation is functorial.  The original soundness
theorem then forms a natural semantic-qualification map from every shadow back
to its source authority.

The qualification is conservative exactly when the source semantics is also
complete for native derivability.  Soundness alone gives only the forward
qualification.  This distinguishes a schematic checker from a semantically
qualified NIK authority without pretending that being a functor, by itself,
establishes semantic provenance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory

universe uKind uSignature uClaim uCertificate

/-! ## The derivability shadow of one authority -/

/-- Retain native proof scope while forgetting the stronger semantic
interpretation of that scope. -/
def derivabilityTheory {Kind : Type uKind}
    (theory : TheoryFamily.{uSignature, uKind, uClaim} Kind) :
    TheoryFamily.{uSignature, uKind, uClaim} Kind where
  Signature := theory.Signature
  signatureOf := theory.signatureOf
  Claim := theory.Claim
  Scope := theory.Scope
  Meaning := theory.Scope
  scope_sound := fun _kind _claim inScope => inScope

@[simp] theorem derivabilityTheory_scope
    {Kind : Type uKind}
    (theory : TheoryFamily.{uSignature, uKind, uClaim} Kind)
    (kind : Kind) (claim : theory.Claim kind) :
    (derivabilityTheory theory).Scope kind claim <-> theory.Scope kind claim :=
  Iff.rfl

@[simp] theorem derivabilityTheory_meaning
    {Kind : Type uKind}
    (theory : TheoryFamily.{uSignature, uKind, uClaim} Kind)
    (kind : Kind) (claim : theory.Claim kind) :
    (derivabilityTheory theory).Meaning kind claim <->
      theory.Scope kind claim :=
  Iff.rfl

/-- The shadow uses the exact original checker and certificate fibres. -/
def derivabilityContract
    {Kind : Type uKind}
    {theory : TheoryFamily.{uSignature, uKind, uClaim} Kind}
    (contract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory) :
    AuthorityContract (derivabilityTheory theory) where
  Certificate := contract.Certificate
  checker := contract.checker
  scopeAuthority := contract.scopeAuthority

@[simp] theorem derivabilityContract_check
    {Kind : Type uKind}
    {theory : TheoryFamily.{uSignature, uKind, uClaim} Kind}
    (contract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory)
    (kind : Kind) (claim : theory.Claim kind)
    (certificate : contract.Certificate kind) :
    ((derivabilityContract contract).checker kind).check claim certificate =
      (contract.checker kind).check claim certificate :=
  rfl

/-- Reattach the original semantics without changing any operational data.
The nontrivial field is exactly the original scope-soundness theorem. -/
def qualification
    {Kind : Type uKind}
    {theory : TheoryFamily.{uSignature, uKind, uClaim} Kind}
    (contract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory) :
    CertifiedTranslation (derivabilityContract contract) contract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind claim => claim
  mapCertificate := fun _kind certificate => certificate
  check_commutes := by intro _kind _claim _certificate; rfl
  meaning_preserved := theory.scope_sound

@[simp] theorem qualification_check_commutes
    {Kind : Type uKind}
    {theory : TheoryFamily.{uSignature, uKind, uClaim} Kind}
    (contract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory)
    (kind : Kind) (claim : theory.Claim kind)
    (certificate : contract.Certificate kind) :
    (contract.checker kind).check
        ((qualification contract).mapClaim kind claim)
        ((qualification contract).mapCertificate kind certificate) =
      ((derivabilityContract contract).checker kind).check claim certificate :=
  (qualification contract).check_commutes kind claim certificate

/-! ## Functoriality and natural semantic qualification -/

/-- Bundle the derivability shadow of one exact authority object. -/
def derivabilityObject
    (object :
      CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}) :
    CertifiedTheory.{uKind, uSignature, uClaim, uCertificate} where
  Kind := object.Kind
  family := derivabilityTheory object.family
  contract := derivabilityContract object.contract

/-- Exact authority translations remain exact after forgetting semantic
meaning, because exact replay already transports proof scope. -/
def derivabilityMap
    {source target :
      CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}}
    (translation : source ⟶ target) :
    derivabilityObject source ⟶ derivabilityObject target where
  mapKind := translation.mapKind
  mapSignature := translation.mapSignature
  signature_commutes := translation.signature_commutes
  mapClaim := translation.mapClaim
  mapCertificate := translation.mapCertificate
  check_commutes := translation.check_commutes
  meaning_preserved := translation.scope_preserved

/-- Replacing semantic meaning by native derivability is an endofunctor on
the category of exact NIK authorities. -/
def derivabilityFunctor :
    CategoryTheory.Functor
      (CertifiedTheory.{uKind, uSignature, uClaim, uCertificate})
      (CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}) where
  obj := derivabilityObject
  map := derivabilityMap
  map_id _object := rfl
  map_comp _earlier _later := rfl

/-- Scope soundness is natural with respect to exact authority translations.
Every component keeps the checker and all certificate data unchanged. -/
def semanticQualification : CategoryTheory.NatTrans derivabilityFunctor
    (CategoryTheory.Functor.id
      (CertifiedTheory.{uKind, uSignature, uClaim, uCertificate})) where
  app object := qualification object.contract
  naturality := by
    intro source target translation
    apply CertifiedTheoryCategory.CertifiedTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      rfl
    · intro kind claim
      exact HEq.rfl
    · intro kind certificate
      exact HEq.rfl

/-! ## Soundness versus semantic completeness -/

/-- Native derivability is semantically complete when every meaningful claim
is also in native proof scope. -/
def SemanticallyComplete
    {Kind : Type uKind}
    (theory : TheoryFamily.{uSignature, uKind, uClaim} Kind) : Prop :=
  forall kind claim, theory.Meaning kind claim -> theory.Scope kind claim

/-- The semantic qualification reflects both scope and meaning exactly iff
the source theory is semantically complete. -/
theorem qualification_conservative_iff
    {Kind : Type uKind}
    {theory : TheoryFamily.{uSignature, uKind, uClaim} Kind}
    (contract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory) :
    (qualification contract).toTheoryTranslation.Conservative <->
      SemanticallyComplete theory := by
  constructor
  · intro conservative kind claim meaningful
    exact conservative.meaning_reflecting kind claim meaningful
  · intro complete
    exact
      { scope_reflecting := by
          intro _kind _claim inScope
          exact inScope
        meaning_reflecting := complete }

/-- One meaningful but unprovable claim is enough to refute conservativity of
the qualification map. -/
theorem qualification_not_conservative_of_semantic_gap
    {Kind : Type uKind}
    {theory : TheoryFamily.{uSignature, uKind, uClaim} Kind}
    (contract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory)
    (kind : Kind) (claim : theory.Claim kind)
    (meaningful : theory.Meaning kind claim)
    (outsideScope : Not (theory.Scope kind claim)) :
    Not ((qualification contract).toTheoryTranslation.Conservative) := by
  intro conservative
  exact outsideScope
    (conservative.meaning_reflecting kind claim meaningful)

/-! ## Object versus functor is not the semantic discriminator -/

namespace CheckerDefinedCanary

open NIKMetalogic.TheoryFamilyCanary

/-- Exact authority for the existing checker-defined theory canary.  It is a
derivability-only object, not evidence of independent semantics. -/
def contract : AuthorityContract checkerDefinedTheory where
  Certificate := fun _kind => Unit
  checker := fun _kind => priorChecker
  scopeAuthority := fun _kind =>
    { sound := by
        intro claim certificate accepted
        exact ⟨certificate, accepted⟩
      complete := by
        intro claim inScope
        exact inScope }

def object : CertifiedTheory where
  Kind := Unit
  family := checkerDefinedTheory
  contract := contract

/-- Even a checker-defined object induces a genuine constant functor.  Hence
mere functoriality cannot certify that meaning was independently authored. -/
def constantFunctor : CategoryTheory.Functor
    (CategoryTheory.Discrete Bool) CertifiedTheory :=
  (CategoryTheory.Functor.const (CategoryTheory.Discrete Bool)).obj object

theorem constantFunctor_meaning_iff_checker_accepts
    (index : CategoryTheory.Discrete Bool) (claim : Bool) :
    (constantFunctor.obj index).family.Meaning () claim <->
      Exists fun certificate => priorChecker.check claim certificate = true :=
  Iff.rfl

theorem constantFunctor_rejects_false
    (index : CategoryTheory.Discrete Bool) :
    Not ((constantFunctor.obj index).family.Meaning () false) :=
  NIKMetalogic.TheoryFamilyCanary.false_not_meaning

end CheckerDefinedCanary

/-! ## Concrete semantic-gap control -/

namespace SemanticGapCanary

/-- Proof scope contains only `true`; semantic meaning recognizes either
Boolean value.  The disjunction is intentional semantic content, not a
placeholder proposition. -/
def theory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Bool
  Scope := fun _kind claim => claim = true
  Meaning := fun _kind claim => Or (claim = true) (claim = false)
  scope_sound := by
    intro _kind claim inScope
    exact Or.inl inScope

def checker : Checker Bool Unit where
  check claim _certificate := claim

def contract : AuthorityContract theory where
  Certificate := fun _kind => Unit
  checker := fun _kind => checker
  scopeAuthority := fun _kind =>
    { sound := by
        intro claim _certificate accepted
        exact accepted
      complete := by
        intro claim inScope
        change claim = true at inScope
        exact ⟨(), by
          change claim = true
          exact inScope⟩ }

theorem true_is_in_scope : theory.Scope () true :=
  rfl

theorem false_is_meaningful : theory.Meaning () false :=
  Or.inr rfl

theorem false_is_not_in_scope : Not (theory.Scope () false) := by
  simp [theory]

theorem qualification_is_not_conservative :
    Not ((qualification contract).toTheoryTranslation.Conservative) :=
  qualification_not_conservative_of_semantic_gap contract () false
    false_is_meaningful false_is_not_in_scope

end SemanticGapCanary

#print axioms derivabilityTheory_meaning
#print axioms derivabilityContract_check
#print axioms qualification_check_commutes
#print axioms derivabilityFunctor
#print axioms semanticQualification
#print axioms qualification_conservative_iff
#print axioms qualification_not_conservative_of_semantic_gap
#print axioms CheckerDefinedCanary.constantFunctor_meaning_iff_checker_accepts
#print axioms CheckerDefinedCanary.constantFunctor_rejects_false
#print axioms SemanticGapCanary.true_is_in_scope
#print axioms SemanticGapCanary.false_is_meaningful
#print axioms SemanticGapCanary.false_is_not_in_scope
#print axioms SemanticGapCanary.qualification_is_not_conservative

end Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification
