import Mettapedia.GSLT.LanguageDef.BiformTheory
import Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget
import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory

/-!
# The certificate boundary of a biform theory

A biform theory relates every retained algorithmic event to a theorem of its
native closed theory, and a proof calculus supplies the native proof fibre of
that theorem.  Neither manufactures an executable checker.  This module adds
exactly that: a certificate boundary is an independent checker proved
fibrewise equivalent to the native calculus, which is the fourth of the four
NIK service faces, the external certificate boundary, and nothing more.

Certified biform theories and their routes form a category.  A route
transports the biform theory and its certificates together; certificate
replay uses the sentence map already selected by the biform route.  The
negative control shows that a checker accepting a single token can preserve
theorem existence while erasing distinct native proofs, so it is not an
exact boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uSignature uHom uSentence uTerm uCertificate

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}

/-! ## Native proof fibres of event meanings -/

/-- Native proofs of the sentence assigned to one retained operational event. -/
def EventMeaningProofFibre
    (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution)
    (calculus : PiInstitution.ProofCalculus institution)
    (event : theory.algorithm.Event) :=
  ClosedTheorySemanticTarget.ProofFibre
    (ClosedTheorySemanticTarget.evidenceDiscipline calculus theory.logical)
    (theory.meaning event)

/-- Every retained biform event has a native proof of its assigned meaning. -/
theorem eventMeaningProofFibre_nonempty
    (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution)
    (calculus : PiInstitution.ProofCalculus institution)
    (event : theory.algorithm.Event) :
    Nonempty (EventMeaningProofFibre theory calculus event) := by
  rw [EventMeaningProofFibre,
    ClosedTheorySemanticTarget.proofFibre_nonempty_iff_scope]
  exact theory.meaning_sound event

/-! ## Adding an exact certificate boundary -/

/-- A biform theory becomes proof-carrying at the NIK boundary only after an
independent checker is proved fibrewise equivalent to its native calculus. -/
structure CertificateBoundary
    (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution)
    (calculus : PiInstitution.ProofCalculus institution) where
  contract : ProofCarryingAuthority.{0, uCertificate}
    (ClosedTheorySemanticTarget.evidenceDiscipline calculus theory.logical)

namespace CertificateBoundary

variable
  {theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
  {calculus : PiInstitution.ProofCalculus institution}

/-- Forget native proof identity only after deriving the exact replay contract. -/
def toAuthorityContract
    (realization :
      CertificateBoundary.{uSignature, uHom, uSentence, uTerm,
        uCertificate} theory calculus) :
    AuthorityContract
      (ClosedTheorySemanticTarget.theoryFamily theory.logical) :=
  realization.contract.toAuthorityContract

/-- Every retained event meaning has an accepted primary certificate. -/
theorem eventMeaning_has_accepted_certificate
    (realization :
      CertificateBoundary.{uSignature, uHom, uSentence, uTerm,
        uCertificate} theory calculus)
    (event : theory.algorithm.Event) :
    ∃ certificate : realization.contract.Certificate (),
      (realization.contract.checker ()).check
          (theory.meaning event) certificate = true := by
  exact (realization.contract.scopeAuthority ()).complete
    (theory.meaning event) (theory.meaning_sound event)

end CertificateBoundary

/-! ## Negative control: theorem existence does not preserve proof identity -/

/-- A checker whose raw certificate type is `Unit` cannot be an exact primary
boundary for a theorem carrying the two distinct proofs of the tagged native
calculus. -/
theorem no_unit_certificate_equivalence_for_tagged_theorem
    (logical : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj logical.signature)
    (theoremhood : formula ∈ logical.theory.1)
    (checker : Checker
      (institution.sentence.obj logical.signature) Unit) :
    IsEmpty (CertificateEquivalence checker
      ((ClosedTheorySemanticTarget.taggedDiscipline logical).proofSystem ())) :=
  ⟨by
    intro boundary
    let falseProof :
        ((ClosedTheorySemanticTarget.taggedDiscipline logical).proofSystem ())
          |>.ProofFibre formula :=
      ⟨(⟨formula, theoremhood⟩, false), rfl⟩
    let trueProof :
        ((ClosedTheorySemanticTarget.taggedDiscipline logical).proofSystem ())
          |>.ProofFibre formula :=
      ⟨(⟨formula, theoremhood⟩, true), rfl⟩
    let falseAccepted := (boundary.fibreEquiv formula).symm falseProof
    let trueAccepted := (boundary.fibreEquiv formula).symm trueProof
    have acceptedEqual : falseAccepted = trueAccepted := by
      apply Subtype.ext
      exact Subsingleton.elim _ _
    have proofEqual : falseProof = trueProof := by
      exact (boundary.fibreEquiv formula).symm.injective acceptedEqual
    have tagEqual := congrArg (fun proof => proof.1.2) proofEqual
    change false = true at tagEqual
    exact Bool.false_ne_true tagEqual⟩

#print axioms EventMeaningProofFibre
#print axioms eventMeaningProofFibre_nonempty
#print axioms CertificateBoundary.toAuthorityContract
#print axioms CertificateBoundary.eventMeaning_has_accepted_certificate
#print axioms no_unit_certificate_equivalence_for_tagged_theorem

end Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary

/-! ## The category of certified biform theories -/

namespace Mettapedia.GSLT.LanguageDef.CertifiedBiformTheory

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary

universe uSignature uHom uSentence uTerm uCertificate

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
  (calculus : PiInstitution.ProofCalculus institution)

/-- A biform theory equipped with an exact primary certificate boundary for
the selected native proof calculus. -/
structure Object where
  biform : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution
  boundary :
    CertificateBoundary.{uSignature, uHom, uSentence, uTerm,
      uCertificate} biform calculus

namespace Object

variable {calculus : PiInstitution.ProofCalculus institution}

/-- The certified theory carried by one certified biform theory: its closed
theory with the replay contract of its certificate boundary. -/
def toCertifiedTheory
    (object : Object.{uSignature, uHom, uSentence, uTerm, uCertificate}
      calculus) :
    CertifiedTheoryCategory.CertifiedTheory.{0, uSignature, uSentence,
      uCertificate} where
  Kind := Unit
  family := ClosedTheorySemanticTarget.theoryFamily object.biform.logical
  contract := object.boundary.toAuthorityContract

end Object

/-! ## Qualified routes -/

variable {calculus : PiInstitution.ProofCalculus institution}

/-- A qualified route transports the biform theory and its executable
certificates together.  Claim transport is not an independent field: it is
the sentence map already selected by the biform route. -/
structure Hom
    (source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus) where
  biform : BiformTheory.Hom source.biform target.biform
  mapCertificate :
    source.boundary.contract.Certificate () →
      target.boundary.contract.Certificate ()
  check_commutes : ∀ formula certificate,
    (target.boundary.contract.checker ()).check
        (institution.sentence.map biform.logical.mapSignature formula)
        (mapCertificate certificate) =
      (source.boundary.contract.checker ()).check formula certificate

namespace Hom

variable
  {first middle last :
    Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus}

/-- Qualified routes are determined by their biform and certificate actions;
the replay equation is proof-irrelevant. -/
@[ext]
theorem ext_data {left right : Hom first middle}
    (biform : left.biform = right.biform)
    (certificate : left.mapCertificate = right.mapCertificate) :
    left = right := by
  cases left
  cases right
  cases biform
  cases certificate
  rfl

/-- Identity changes neither the biform theory nor its certificates. -/
def identity (object :
    Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus) :
    Hom object object where
  biform := BiformTheory.Hom.identity object.biform
  mapCertificate := id
  check_commutes := by
    intro formula certificate
    change (object.boundary.contract.checker ()).check
        (institution.sentence.map
          (CategoryTheory.CategoryStruct.id object.biform.logical.signature)
          formula) certificate =
      (object.boundary.contract.checker ()).check formula certificate
    rw [institution.sentence.map_id_apply]

/-- Composition follows the biform route and then transports the certificate
through both exact replay boundaries. -/
def comp (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last where
  biform := BiformTheory.Hom.comp earlier.biform later.biform
  mapCertificate certificate :=
    later.mapCertificate (earlier.mapCertificate certificate)
  check_commutes := by
    intro formula certificate
    change (last.boundary.contract.checker ()).check
        (institution.sentence.map
          (CategoryTheory.CategoryStruct.comp
            earlier.biform.logical.mapSignature
            later.biform.logical.mapSignature) formula)
        (later.mapCertificate (earlier.mapCertificate certificate)) = _
    rw [institution.sentence.map_comp_apply]
    rw [later.check_commutes]
    rw [earlier.check_commutes]

/-- Forget certificate transport and retain the underlying biform route.
This projection need not be faithful: distinct certificate maps can qualify
the same biform route. -/
def toBiform (route : Hom first middle) :
    BiformTheory.Hom first.biform middle.biform :=
  route.biform

/-- Every certified route induces a certified
translation with the same native sentence map. -/
def toCertifiedTranslation (route : Hom first middle) :
    (first.toCertifiedTheory ⟶ middle.toCertifiedTheory) where
  mapKind := id
  mapSignature := fun _ => .selected
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ formula =>
    institution.sentence.map route.biform.logical.mapSignature formula
  mapCertificate := fun _ certificate => route.mapCertificate certificate
  check_commutes := by
    intro kind formula certificate
    cases kind
    exact route.check_commutes formula certificate
  meaning_preserved := by
    intro kind formula theoremhood
    cases kind
    exact route.biform.logical.preserves theoremhood

end Hom

/-! ## The two categorical projections -/

instance : CategoryTheory.Category
    (Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus) where
  Hom := Hom
  id := Hom.identity
  comp earlier later := Hom.comp earlier later
  id_comp route := by
    apply Hom.ext_data
    · exact BiformTheory.biformTheoryCategory.id_comp route.biform
    · rfl
  comp_id route := by
    apply Hom.ext_data
    · exact BiformTheory.biformTheoryCategory.comp_id route.biform
    · rfl
  assoc earlier middle later := by
    apply Hom.ext_data
    · exact BiformTheory.biformTheoryCategory.assoc earlier.biform
        middle.biform later.biform
    · rfl

/-- Project to the biform theory, forgetting the certificate boundary. -/
def biformProjection :
    Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus ⥤
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution where
  obj object := object.biform
  map route := route.biform
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Project to the certified theory, forgetting the operational face. -/
def certifiedTheoryProjection :
    Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus ⥤
      CertifiedTheoryCategory.CertifiedTheory.{0, uSignature, uSentence,
        uCertificate} where
  obj object := object.toCertifiedTheory
  map route := route.toCertifiedTranslation
  map_id object := by
    apply CertifiedTheoryCategory.CertifiedTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      cases signature
      rfl
    · intro kind formula
      cases kind
      exact heq_of_eq
        (institution.sentence.map_id_apply object.biform.logical.signature
          formula)
    · intro kind certificate
      cases kind
      rfl
  map_comp earlier later := by
    apply CertifiedTheoryCategory.CertifiedTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      cases signature
      rfl
    · intro kind formula
      cases kind
      exact heq_of_eq
        (institution.sentence.map_comp_apply
          earlier.biform.logical.mapSignature
          later.biform.logical.mapSignature formula)
    · intro kind certificate
      cases kind
      rfl

/-! ## Qualification as a compatibility locus -/

/-- The independently readable data of one qualified route. -/
def routePair
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus}
    (route : source ⟶ target) :=
  (route.biform, route.mapCertificate)

/-- A biform route and certificate map are compatible exactly when checker
replay commutes using the biform route's native sentence translation. -/
def ReplayCompatible
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus}
    (pair :
      BiformTheory.Hom source.biform target.biform ×
        (source.boundary.contract.Certificate () →
          target.boundary.contract.Certificate ())) : Prop :=
  ∀ formula certificate,
    (target.boundary.contract.checker ()).check
        (institution.sentence.map pair.1.logical.mapSignature formula)
        (pair.2 certificate) =
      (source.boundary.contract.checker ()).check formula certificate

/-- The image of qualified routes is exactly the replay-compatible locus. -/
theorem routePair_range_iff_replayCompatible
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus}
    (pair :
      BiformTheory.Hom source.biform target.biform ×
        (source.boundary.contract.Certificate () →
          target.boundary.contract.Certificate ())) :
    (∃ route : source ⟶ target, routePair route = pair) ↔
      ReplayCompatible pair := by
  constructor
  · rintro ⟨route, rfl⟩
    exact route.check_commutes
  · intro compatible
    exact ⟨{ biform := pair.1
             mapCertificate := pair.2
             check_commutes := compatible }, rfl⟩

/-- The biform and certificate actions jointly determine a qualified route. -/
theorem routePair_injective
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate} calculus} :
    Function.Injective (routePair : (source ⟶ target) → _) := by
  intro left right equal
  apply Hom.ext_data
  · exact congrArg Prod.fst equal
  · exact congrArg Prod.snd equal

#print axioms Object.toCertifiedTheory
#print axioms Hom.toCertifiedTranslation
#print axioms biformProjection
#print axioms certifiedTheoryProjection
#print axioms routePair_range_iff_replayCompatible
#print axioms routePair_injective

end Mettapedia.GSLT.LanguageDef.CertifiedBiformTheory
