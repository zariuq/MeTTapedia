import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.Languages.TPTP.NIKAuthority

/-!
# Statusful default-NIK frontend for TPTP proof DAGs

The chronological TPTP checker is itself one top-level authority whose local
rule certificates remain dependently indexed by the open rule registry.  This
module places that authority behind the common statusful NIK frontend.
-/

namespace Mettapedia.Languages.TPTP.NIKDefault

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.StatusSemantics

universe uFormula uCertificate

/-- The whole chronological proof, rather than one local rule, is one NIK
authority fibre. -/
def authorityFamily {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics) :
    AuthorityFamily Unit where
  Claim := fun _ => Skeleton Formula
  Certificate := fun _ => List rules.PackedCertificate
  checker := fun _ => proofChecker rules
  Certified := fun _ => Certified rules
  Meaning := fun _ => Meaning rules
  projection := fun _ => proofChecker_authorityProjection rules

inductive Request {Formula : Type uFormula}
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics) where
  | malformed
  | unknownAuthority (name : String)
  | proof (skeleton : Skeleton Formula)
      (certificates : List rules.PackedCertificate)

inductive Parsed {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics) where
  | unknownAuthority (name : String)
  | submission (request : TypedSubmission (authorityFamily rules))

def frontend {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics) :
    Frontend (authorityFamily rules) (Request rules) where
  Parsed := Parsed rules
  parse
    | .malformed => none
    | .unknownAuthority name => some (.unknownAuthority name)
    | .proof skeleton certificates =>
        some (.submission ⟨(), skeleton, certificates⟩)
  resolve
    | .unknownAuthority _ => none
    | .submission request => some request
  encode := fun ⟨_, skeleton, certificates⟩ =>
    .proof skeleton certificates
  resolve_encode := by
    rintro ⟨kind, skeleton, certificates⟩
    cases kind
    exact ⟨.submission ⟨(), skeleton, certificates⟩, rfl, rfl⟩

def machine {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics) :
    Refinement.Machine (frontend rules) :=
  Refinement.atomic (frontend rules)

@[simp] theorem malformed_status {Formula : Type uFormula}
    [DecidableEq Formula] {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics) :
    (frontend rules).run .malformed = .malformed :=
  rfl

@[simp] theorem unknown_authority_status {Formula : Type uFormula}
    [DecidableEq Formula] {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics)
    (name : String) :
    (frontend rules).run (.unknownAuthority name) = .unsupported :=
  rfl

theorem proof_status {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics)
    (skeleton : Skeleton Formula)
    (certificates : List rules.PackedCertificate) :
    (frontend rules).run (.proof skeleton certificates) =
      if (proofChecker rules).check skeleton certificates then
        .accepted ⟨(), skeleton⟩
      else
        .rejected ⟨(), skeleton⟩ := by
  cases checked : (proofChecker rules).check skeleton certificates <;>
    simp [frontend, Frontend.run, checked, TypedSubmission.claim,
      authorityFamily]

theorem accepted_proof {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics)
    (skeleton : Skeleton Formula)
    (certificates : List rules.PackedCertificate)
    (accepted : (proofChecker rules).check skeleton certificates = true) :
    (frontend rules).run (.proof skeleton certificates) =
      .accepted ⟨(), skeleton⟩ := by
  simpa [accepted] using proof_status rules skeleton certificates

theorem rejected_proof {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics)
    (skeleton : Skeleton Formula)
    (certificates : List rules.PackedCertificate)
    (rejected : (proofChecker rules).check skeleton certificates = false) :
    (frontend rules).run (.proof skeleton certificates) =
      .rejected ⟨(), skeleton⟩ := by
  simpa [rejected] using proof_status rules skeleton certificates

/-- Exact certificate completeness of the chronological proof authority
survives the common statusful frontend. -/
theorem certified_iff_exists_accepted_request
    {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily.{uFormula, uCertificate} Formula semantics)
    (skeleton : Skeleton Formula) :
    Certified rules skeleton ↔
      ∃ certificates : List rules.PackedCertificate,
        (frontend rules).run (.proof skeleton certificates) =
          .accepted ⟨(), skeleton⟩ := by
  simpa [frontend, authorityFamily, AuthorityFamily.packedCertified] using
    (frontend rules).certified_iff_exists_accepted_request
      (⟨(), skeleton⟩ : (authorityFamily rules).PackedClaim)

/-! ## Existing finite semantic instance through the default protocol -/

namespace Canary

open Mettapedia.Languages.TPTP.NIKAuthority.Canary

theorem valid_proof_accepted_by_default :
    (frontend finiteRuleFamily).run (.proof validSkeleton validEvidence) =
      .accepted ⟨(), validSkeleton⟩ :=
  accepted_proof finiteRuleFamily validSkeleton validEvidence
    valid_proof_accepted

theorem wrong_status_rejected_by_default :
    (frontend finiteRuleFamily).run
        (.proof validSkeleton wrongStatusEvidence) =
      .rejected ⟨(), validSkeleton⟩ :=
  rejected_proof finiteRuleFamily validSkeleton wrongStatusEvidence
    wrong_status_rejected

theorem missing_parent_rejected_by_default :
    (frontend finiteRuleFamily).run
        (.proof missingParentSkeleton validEvidence) =
      .rejected ⟨(), missingParentSkeleton⟩ :=
  rejected_proof finiteRuleFamily missingParentSkeleton validEvidence
    missing_parent_rejected

theorem malformed_and_unknown_are_distinct :
    (frontend finiteRuleFamily).run .malformed = .malformed ∧
      (frontend finiteRuleFamily).run (.unknownAuthority "not-installed") =
        .unsupported :=
  ⟨rfl, rfl⟩

end Canary

end Mettapedia.Languages.TPTP.NIKDefault
