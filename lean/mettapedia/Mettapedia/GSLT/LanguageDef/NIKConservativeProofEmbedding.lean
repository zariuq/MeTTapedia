import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

/-!
# Conservative proof embeddings between heterogeneous NIK authorities

Exact Boolean replay is necessary for translating one proof authority into
another, but it is not sufficient for calling the translation an embedding.
A translation may preserve every acceptance result while collapsing distinct
claims or distinct accepted certificates.

This module isolates the stronger comparison used for bootstrap hosts.  A
`ConservativeProofEmbedding` requires:

* injectivity of the authority-kind map;
* injectivity of each translated claim fibre;
* bijectivity of the induced map on accepted-certificate fibres; and
* reflection, as well as preservation, of independently supplied meaning.

Surjectivity on accepted fibres derives theorem-scope reflection.  Consequently
the underlying theory translation is conservative, while proof occurrence
identity is retained rather than reconstructed from theorem existence.

The positive example changes both claim and certificate representations.  Two
negative examples show separately that exact checker commutation can erase
certificate identity and that exact accepted-fibre parity can still collapse
claim identity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKConservativeProofEmbedding

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe uKind uSignature uClaim uCertificate

section Generic

variable {SourceKind MiddleKind TargetKind : Type uKind}
    {source : TheoryFamily.{uSignature, uKind, uClaim} SourceKind}
    {middle : TheoryFamily.{uSignature, uKind, uClaim} MiddleKind}
    {target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind}
    {sourceContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} source}
    {middleContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} middle}
    {targetContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} target}

/-- Exact replay induces a map between the accepted-certificate fibres of a
source claim and its translated target claim. -/
def acceptedMap
    (translation : CertifiedTranslation sourceContract targetContract)
    (kind : SourceKind) (claim : source.Claim kind) :
    AcceptedCertificateFibre (sourceContract.checker kind) claim ->
      AcceptedCertificateFibre
        (targetContract.checker (translation.mapKind kind))
        (translation.mapClaim kind claim) :=
  fun accepted =>
    ⟨translation.mapCertificate kind accepted.1, by
      rw [translation.check_commutes]
      exact accepted.2⟩

@[simp] theorem acceptedMap_certificate
    (translation : CertifiedTranslation sourceContract targetContract)
    (kind : SourceKind) (claim : source.Claim kind)
    (accepted :
      AcceptedCertificateFibre (sourceContract.checker kind) claim) :
    (acceptedMap translation kind claim accepted).1 =
      translation.mapCertificate kind accepted.1 :=
  rfl

/-- Accepted-certificate transport follows composition of authority
translations. -/
theorem acceptedMap_comp
    (earlier : CertifiedTranslation sourceContract middleContract)
    (later : CertifiedTranslation middleContract targetContract)
    (kind : SourceKind) (claim : source.Claim kind)
    (accepted :
      AcceptedCertificateFibre (sourceContract.checker kind) claim) :
    acceptedMap (CertifiedTranslation.comp earlier later) kind claim accepted =
      acceptedMap later (earlier.mapKind kind) (earlier.mapClaim kind claim)
        (acceptedMap earlier kind claim accepted) := by
  apply Subtype.ext
  rfl

/-- A conservative proof embedding retains the identities relevant to a NIK
authority, not only its yes/no theorem set.  `certificate_bijective` is stated
on accepted fibres so rejected wire decorations are not promoted into proof
identity. -/
structure ConservativeProofEmbedding
    (translation : CertifiedTranslation sourceContract targetContract) : Prop where
  kind_injective : Function.Injective translation.mapKind
  claim_injective : forall kind,
    Function.Injective (translation.mapClaim kind)
  certificate_bijective : forall kind claim,
    Function.Bijective (acceptedMap translation kind claim)
  meaning_reflecting : forall kind claim,
    target.Meaning (translation.mapKind kind)
        (translation.mapClaim kind claim) ->
      source.Meaning kind claim

namespace ConservativeProofEmbedding

/-- Fullness on accepted certificates reflects theorem scope.  This is why
scope reflection need not be a redundant field of the embedding. -/
theorem scope_reflecting
    {translation : CertifiedTranslation sourceContract targetContract}
    (embedding : ConservativeProofEmbedding translation)
    (kind : SourceKind) (claim : source.Claim kind)
    (inTargetScope :
      target.Scope (translation.mapKind kind)
        (translation.mapClaim kind claim)) :
    source.Scope kind claim := by
  obtain ⟨targetCertificate, targetAccepted⟩ :=
    (targetContract.scopeAuthority (translation.mapKind kind)).complete
      (translation.mapClaim kind claim) inTargetScope
  let acceptedTarget : AcceptedCertificateFibre
      (targetContract.checker (translation.mapKind kind))
      (translation.mapClaim kind claim) :=
    ⟨targetCertificate, targetAccepted⟩
  obtain ⟨acceptedSource, _mapsToTarget⟩ :=
    (embedding.certificate_bijective kind claim).2 acceptedTarget
  exact (sourceContract.scopeAuthority kind).sound
    claim acceptedSource.1 acceptedSource.2

/-- Forgetting certificate identity from a conservative proof embedding yields
a conservative heterogeneous theory translation. -/
def toTheoryConservative
    {translation : CertifiedTranslation sourceContract targetContract}
    (embedding : ConservativeProofEmbedding translation) :
    translation.toTheoryTranslation.Conservative where
  scope_reflecting := embedding.scope_reflecting
  meaning_reflecting := embedding.meaning_reflecting

/-- Translated claims have exactly the same theorem scope. -/
theorem scope_iff
    {translation : CertifiedTranslation sourceContract targetContract}
    (embedding : ConservativeProofEmbedding translation)
    (kind : SourceKind) (claim : source.Claim kind) :
    target.Scope (translation.mapKind kind)
        (translation.mapClaim kind claim) <->
      source.Scope kind claim :=
  TheoryTranslation.scope_iff_of_conservative
    translation.toTheoryTranslation embedding.toTheoryConservative kind claim

/-- Rejection of a translated claim is equivalent to rejection of its source.
In particular, when `claim` is the distinguished contradiction of a bootstrap
profile, a conservative proof embedding transports syntactic consistency in
both directions. -/
theorem scope_rejection_iff
    {translation : CertifiedTranslation sourceContract targetContract}
    (embedding : ConservativeProofEmbedding translation)
    (kind : SourceKind) (claim : source.Claim kind) :
    (¬ target.Scope (translation.mapKind kind)
        (translation.mapClaim kind claim)) <->
      ¬ source.Scope kind claim :=
  not_congr (embedding.scope_iff kind claim)

/-- Translated claims have exactly the same independently supplied meaning. -/
theorem meaning_iff
    {translation : CertifiedTranslation sourceContract targetContract}
    (embedding : ConservativeProofEmbedding translation)
    (kind : SourceKind) (claim : source.Claim kind) :
    target.Meaning (translation.mapKind kind)
        (translation.mapClaim kind claim) <->
      source.Meaning kind claim :=
  TheoryTranslation.meaning_iff_of_conservative
    translation.toTheoryTranslation embedding.toTheoryConservative kind claim

/-- Accepted source and target proof fibres are equivalent, rather than merely
equi-inhabited. -/
noncomputable def acceptedFibreEquiv
    {translation : CertifiedTranslation sourceContract targetContract}
    (embedding : ConservativeProofEmbedding translation)
    (kind : SourceKind) (claim : source.Claim kind) :
    AcceptedCertificateFibre (sourceContract.checker kind) claim ≃
      AcceptedCertificateFibre
        (targetContract.checker (translation.mapKind kind))
        (translation.mapClaim kind claim) :=
  Equiv.ofBijective (acceptedMap translation kind claim)
    (embedding.certificate_bijective kind claim)

/-- Identity is a conservative proof embedding. -/
def identity (contract :
    AuthorityContract.{uKind, uCertificate, uSignature, uClaim} source) :
    ConservativeProofEmbedding (CertifiedTranslation.identity contract) where
  kind_injective := by intro left right equality; exact equality
  claim_injective := by
    intro kind left right equality
    exact equality
  certificate_bijective := by
    intro kind claim
    constructor
    · intro left right equality
      simpa [acceptedMap,
        CertifiedTranslation.identity] using equality
    · intro targetAccepted
      exact ⟨targetAccepted, by
        apply Subtype.ext
        rfl⟩
  meaning_reflecting := by
    intro kind claim meaningful
    exact meaningful

/-- Conservative proof embeddings compose.  Thus a chain through Pure,
OpenTheory, MMB, or another exchange layer can be audited one arrow at a time. -/
def comp
    {earlier : CertifiedTranslation sourceContract middleContract}
    {later : CertifiedTranslation middleContract targetContract}
    (earlierEmbedding : ConservativeProofEmbedding earlier)
    (laterEmbedding : ConservativeProofEmbedding later) :
    ConservativeProofEmbedding (CertifiedTranslation.comp earlier later) where
  kind_injective :=
    laterEmbedding.kind_injective.comp earlierEmbedding.kind_injective
  claim_injective := by
    intro kind
    exact (laterEmbedding.claim_injective (earlier.mapKind kind)).comp
      (earlierEmbedding.claim_injective kind)
  certificate_bijective := by
    intro kind claim
    constructor
    · intro left right equality
      apply (earlierEmbedding.certificate_bijective kind claim).1
      apply (laterEmbedding.certificate_bijective
        (earlier.mapKind kind) (earlier.mapClaim kind claim)).1
      rw [acceptedMap_comp, acceptedMap_comp] at equality
      exact equality
    · intro targetAccepted
      obtain ⟨middleAccepted, middleMaps⟩ :=
        (laterEmbedding.certificate_bijective
          (earlier.mapKind kind) (earlier.mapClaim kind claim)).2
          targetAccepted
      obtain ⟨sourceAccepted, sourceMaps⟩ :=
        (earlierEmbedding.certificate_bijective kind claim).2 middleAccepted
      refine ⟨sourceAccepted, ?_⟩
      rw [acceptedMap_comp, sourceMaps, middleMaps]
  meaning_reflecting := by
    intro kind claim meaningful
    exact earlierEmbedding.meaning_reflecting kind claim
      (laterEmbedding.meaning_reflecting
        (earlier.mapKind kind) (earlier.mapClaim kind claim) meaningful)

end ConservativeProofEmbedding

end Generic

/-! ## A non-identity-shaped positive calibration -/

namespace RepresentationChangeCanary

inductive Kind where
  | only
deriving DecidableEq, Repr

abbrev sourceTheory : TheoryFamily Kind where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Bool
  Scope := fun _ claim => claim = true
  Meaning := fun _ claim => claim = true
  scope_sound := by intro kind claim inScope; exact inScope

abbrev sourceContract : AuthorityContract sourceTheory where
  Certificate := fun _ => Bool
  checker
    | .only => { check := fun claim _certificate => claim }
  scopeAuthority
    | .only =>
      { sound := by intro claim certificate accepted; simpa using accepted
        complete := by
          intro claim inScope
          exact ⟨false, by simpa using inScope⟩ }

abbrev targetTheory : TheoryFamily Kind where
  Signature := Bool
  signatureOf := fun _ => false
  Claim := fun _ => Nat
  Scope := fun _ claim => claim = 0
  Meaning := fun _ claim => claim = 0
  scope_sound := by intro kind claim inScope; exact inScope

abbrev targetContract : AuthorityContract targetTheory where
  Certificate := fun _ => Bool × Unit
  checker
    | .only => { check := fun claim _certificate => decide (claim = 0) }
  scopeAuthority
    | .only =>
      { sound := by intro claim certificate accepted; simpa using accepted
        complete := by
          intro claim inScope
          exact ⟨(false, ()), by simpa using inScope⟩ }

/-- A real representation change: Boolean claims become `0`/`1`, and Boolean
certificates acquire a unit record field. -/
def translation : CertifiedTranslation sourceContract targetContract where
  mapKind := id
  mapSignature := fun _ => false
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ claim => if claim then 0 else 1
  mapCertificate := fun _ certificate => (certificate, ())
  check_commutes := by
    intro kind claim certificate
    cases kind
    cases claim <;> rfl
  meaning_preserved := by
    intro kind claim meaningful
    cases kind
    cases claim <;> simp_all

theorem translation_claim_injective :
    Function.Injective (translation.mapClaim Kind.only) := by
  intro left right equality
  cases left <;> cases right <;> simp_all [translation]

/-- Positive control: the representation-changing translation is a
conservative proof embedding, not an identity masquerading as one. -/
def proofEmbedding : ConservativeProofEmbedding translation where
  kind_injective := by
    intro left right equality
    exact equality
  claim_injective := by
    intro kind
    cases kind
    exact translation_claim_injective
  certificate_bijective := by
    intro kind claim
    cases kind
    cases claim with
    | false =>
        constructor
        · intro left right
          rcases left with ⟨left, accepted⟩
          simp at accepted
        · intro targetAccepted
          rcases targetAccepted with ⟨targetCertificate, accepted⟩
          simp [targetContract, translation] at accepted
    | true =>
        constructor
        · intro left right equality
          apply Subtype.ext
          exact congrArg (fun accepted => accepted.1.1) equality
        · intro targetAccepted
          rcases targetAccepted with ⟨⟨tag, unitValue⟩, accepted⟩
          cases unitValue
          refine ⟨⟨tag, rfl⟩, ?_⟩
          apply Subtype.ext
          rfl
  meaning_reflecting := by
    intro kind claim meaningful
    cases kind
    cases claim <;> simp_all [translation]

theorem true_scope_roundtrip :
    targetTheory.Scope Kind.only (translation.mapClaim Kind.only true) <->
      sourceTheory.Scope Kind.only true :=
  proofEmbedding.scope_iff Kind.only true

end RepresentationChangeCanary

/-! ## Exact replay can erase proof identity -/

namespace CertificateCollapseCanary

open RepresentationChangeCanary

abbrev erasedContract : AuthorityContract sourceTheory where
  Certificate := fun _ => Unit
  checker
    | .only => { check := fun claim _certificate => claim }
  scopeAuthority
    | .only =>
      { sound := by intro claim certificate accepted; simpa using accepted
        complete := by
          intro claim inScope
          exact ⟨(), by simpa using inScope⟩ }

/-- Both Boolean certificate occurrences are erased to the same unit value,
even though every checker result and every meaning is preserved exactly. -/
def erasingTranslation : CertifiedTranslation sourceContract erasedContract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ claim => claim
  mapCertificate := fun _ _certificate => ()
  check_commutes := by intro kind claim certificate; cases kind; rfl
  meaning_preserved := by intro kind claim meaningful; exact meaningful

theorem erasingTranslation_semantically_conservative :
    erasingTranslation.toTheoryTranslation.Conservative where
  scope_reflecting := by intro kind claim inScope; exact inScope
  meaning_reflecting := by intro kind claim meaningful; exact meaningful

/-- Negative control: exact replay plus two-way theorem/meaning preservation
does not preserve proof occurrence identity. -/
theorem erasingTranslation_not_proofEmbedding :
    ¬ ConservativeProofEmbedding erasingTranslation := by
  intro embedding
  let left : AcceptedCertificateFibre
      (sourceContract.checker Kind.only) true := ⟨false, rfl⟩
  let right : AcceptedCertificateFibre
      (sourceContract.checker Kind.only) true := ⟨true, rfl⟩
  have mappedEqual :
      acceptedMap erasingTranslation Kind.only true left =
        acceptedMap erasingTranslation Kind.only true right := by
    apply Subtype.ext
    rfl
  have sourceEqual : left = right :=
    (embedding.certificate_bijective Kind.only true).1 mappedEqual
  have falseEqualsTrue := congrArg (fun accepted => accepted.1) sourceEqual
  exact Bool.false_ne_true falseEqualsTrue

end CertificateCollapseCanary

/-! ## Proof-fibre parity can erase claim identity -/

namespace ClaimCollapseCanary

inductive SourceKind where
  | only
deriving DecidableEq, Repr

inductive TargetKind where
  | only
deriving DecidableEq, Repr

abbrev sourceTheory : TheoryFamily SourceKind where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Bool
  Scope := fun _ _claim => True
  Meaning := fun _ _claim => True
  scope_sound := by intro kind claim inScope; trivial

abbrev targetTheory : TheoryFamily TargetKind where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Unit
  Scope := fun _ _claim => True
  Meaning := fun _ _claim => True
  scope_sound := by intro kind claim inScope; trivial

abbrev sourceContract : AuthorityContract sourceTheory where
  Certificate := fun _ => Unit
  checker
    | .only => { check := fun _claim _certificate => true }
  scopeAuthority
    | .only =>
      { sound := by intro claim certificate accepted; trivial
        complete := by intro claim inScope; exact ⟨(), rfl⟩ }

abbrev targetContract : AuthorityContract targetTheory where
  Certificate := fun _ => Unit
  checker
    | .only => { check := fun _claim _certificate => true }
  scopeAuthority
    | .only =>
      { sound := by intro claim certificate accepted; trivial
        complete := by intro claim inScope; exact ⟨(), rfl⟩ }

/-- Every accepted certificate transports bijectively, but both Boolean claims
are mapped to the same unit claim. -/
def collapsingTranslation :
    CertifiedTranslation sourceContract targetContract where
  mapKind := fun _ => .only
  mapSignature := id
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ _claim => ()
  mapCertificate := fun _ certificate => certificate
  check_commutes := by intro kind claim certificate; cases kind; rfl
  meaning_preserved := by intro kind claim meaningful; trivial

theorem acceptedMap_bijective (claim : Bool) :
    Function.Bijective
      (acceptedMap collapsingTranslation SourceKind.only claim) := by
  constructor
  · intro left right equality
    apply Subtype.ext
    exact Subsingleton.elim _ _
  · intro targetAccepted
    exact ⟨⟨(), rfl⟩, by
      apply Subtype.ext
      exact Subsingleton.elim _ _⟩

/-- Negative control: fibrewise proof parity does not repair a non-injective
claim translation. -/
theorem collapsingTranslation_not_proofEmbedding :
    ¬ ConservativeProofEmbedding collapsingTranslation := by
  intro embedding
  have collision :
      collapsingTranslation.mapClaim SourceKind.only false =
        collapsingTranslation.mapClaim SourceKind.only true := rfl
  exact Bool.false_ne_true
    (embedding.claim_injective SourceKind.only collision)

end ClaimCollapseCanary

#print axioms acceptedMap_comp
#print axioms ConservativeProofEmbedding.scope_reflecting
#print axioms ConservativeProofEmbedding.toTheoryConservative
#print axioms ConservativeProofEmbedding.scope_rejection_iff
#print axioms ConservativeProofEmbedding.comp
#print axioms RepresentationChangeCanary.proofEmbedding
#print axioms CertificateCollapseCanary.erasingTranslation_not_proofEmbedding
#print axioms ClaimCollapseCanary.acceptedMap_bijective
#print axioms ClaimCollapseCanary.collapsingTranslation_not_proofEmbedding

end Mettapedia.GSLT.LanguageDef.NIKConservativeProofEmbedding
