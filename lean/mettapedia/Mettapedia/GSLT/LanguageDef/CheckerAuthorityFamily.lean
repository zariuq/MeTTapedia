import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Indexed families of checker authorities

One NIK entry point need not impose one claim language or one certificate
format.  An indexed authority family retains a distinct dependent claim,
certificate, exact certificate scope, and projected meaning for every
judgment kind.  Packing the family gives a single fail-closed dispatcher.

The kind tag is semantic data.  Evidence tagged for one authority is rejected
when presented to another; it is never coerced by representation coincidence.
-/

namespace Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily

open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uKind uClaim uCertificate
universe uLeftKind uRightKind uLeftClaim uRightClaim
  uLeftCertificate uRightCertificate

/-- A dependent family of independently exact certificate scopes, each with
a proved projection into its guest semantic meaning. -/
structure AuthorityFamily (Kind : Type uKind) where
  Claim : Kind -> Type uClaim
  Certificate : Kind -> Type uCertificate
  checker : (kind : Kind) -> Checker (Claim kind) (Certificate kind)
  Certified : (kind : Kind) -> Claim kind -> Prop
  Meaning : (kind : Kind) -> Claim kind -> Prop
  projection : (kind : Kind) ->
    (checker kind).AuthorityProjection (Certified kind) (Meaning kind)

namespace AuthorityFamily

variable {Kind : Type uKind} (family : AuthorityFamily Kind)

/-- A claim carrying the identity of the authority that gives it meaning. -/
abbrev PackedClaim := Sigma family.Claim

/-- Evidence carrying the identity of the authority that must replay it. -/
abbrev PackedCertificate := Sigma family.Certificate

def packedCertified (claim : family.PackedClaim) : Prop :=
  family.Certified claim.1 claim.2

def packedMeaning (claim : family.PackedClaim) : Prop :=
  family.Meaning claim.1 claim.2

/-- One fail-closed dispatcher for the whole family.  A certificate is
transported only after its kind tag is proved equal to the claim's tag. -/
def packedChecker [DecidableEq Kind] :
    Checker family.PackedClaim family.PackedCertificate where
  check := fun claim certificate =>
    if sameKind : certificate.1 = claim.1 then
      (family.checker claim.1).check claim.2 (sameKind ▸ certificate.2)
    else
      false

@[simp] theorem packedChecker_sameKind [DecidableEq Kind]
    (kind : Kind) (claim : family.Claim kind)
    (certificate : family.Certificate kind) :
    family.packedChecker.check ⟨kind, claim⟩ ⟨kind, certificate⟩ =
      (family.checker kind).check claim certificate := by
  simp [packedChecker]

/-- Cross-authority evidence is rejected even when both payload types happen
to have compatible runtime representations. -/
theorem packedChecker_rejects_wrongKind [DecidableEq Kind]
    {claimKind certificateKind : Kind}
    (different : certificateKind ≠ claimKind)
    (claim : family.Claim claimKind)
    (certificate : family.Certificate certificateKind) :
    family.packedChecker.check ⟨claimKind, claim⟩
      ⟨certificateKind, certificate⟩ = false := by
  simp [packedChecker, different]

theorem packedChecker_sound [DecidableEq Kind] :
    family.packedChecker.Sound family.packedCertified := by
  rintro ⟨claimKind, claim⟩ ⟨certificateKind, certificate⟩ accepted
  simp only [packedChecker] at accepted
  split at accepted
  next sameKind =>
    subst certificateKind
    exact (family.projection claimKind).authority.sound
      claim certificate accepted
  next different =>
    simp at accepted

theorem packedChecker_complete [DecidableEq Kind] :
    family.packedChecker.CertificateComplete family.packedCertified := by
  rintro ⟨kind, claim⟩ certified
  obtain ⟨certificate, accepted⟩ :=
    (family.projection kind).authority.complete claim certified
  exact ⟨⟨kind, certificate⟩, by
    simpa using accepted⟩

/-- The packed dispatcher is exact for the dependent sum of all declared
certificate scopes. -/
theorem packedChecker_authority [DecidableEq Kind] :
    family.packedChecker.Authority family.packedCertified where
  sound := family.packedChecker_sound
  complete := family.packedChecker_complete

theorem packedCertified_implies_meaning
    (claim : family.PackedClaim) :
    family.packedCertified claim -> family.packedMeaning claim := by
  intro certified
  exact (family.projection claim.1).project claim.2 certified

/-- The single packed dispatcher retains the authority-projection guarantee
of every component. -/
def packedAuthorityProjection [DecidableEq Kind] :
    family.packedChecker.AuthorityProjection
      family.packedCertified family.packedMeaning where
  authority := family.packedChecker_authority
  project := family.packedCertified_implies_meaning

/-! ## Composing independently admitted authority families -/

/-- Disjointly compose two dependent authority families.  Claims and
certificates retain their side tag, so evidence from one family cannot be
replayed by the other even when payload representations happen to coincide. -/
def sum
    {LeftKind : Type uLeftKind} {RightKind : Type uRightKind}
    (left : AuthorityFamily.{uLeftKind, uLeftClaim, uLeftCertificate}
      LeftKind)
    (right : AuthorityFamily.{uRightKind, uRightClaim, uRightCertificate}
      RightKind) :
    AuthorityFamily.{max uLeftKind uRightKind, max uLeftClaim uRightClaim,
      max uLeftCertificate uRightCertificate} (Sum LeftKind RightKind) where
  Claim
    | .inl kind => ULift.{uRightClaim} (left.Claim kind)
    | .inr kind => ULift.{uLeftClaim} (right.Claim kind)
  Certificate
    | .inl kind => ULift.{uRightCertificate} (left.Certificate kind)
    | .inr kind => ULift.{uLeftCertificate} (right.Certificate kind)
  checker
    | .inl kind =>
        { check := fun claim certificate =>
            (left.checker kind).check claim.down certificate.down }
    | .inr kind =>
        { check := fun claim certificate =>
            (right.checker kind).check claim.down certificate.down }
  Certified
    | .inl kind => fun claim => left.Certified kind claim.down
    | .inr kind => fun claim => right.Certified kind claim.down
  Meaning
    | .inl kind => fun claim => left.Meaning kind claim.down
    | .inr kind => fun claim => right.Meaning kind claim.down
  projection
    | .inl kind =>
        { authority :=
            { sound := by
                intro claim certificate accepted
                exact (left.projection kind).authority.sound
                  claim.down certificate.down accepted
              complete := by
                intro claim certified
                obtain ⟨certificate, accepted⟩ :=
                  (left.projection kind).authority.complete
                    claim.down certified
                exact ⟨ULift.up certificate, accepted⟩ }
          project := by
            intro claim certified
            exact (left.projection kind).project claim.down certified }
    | .inr kind =>
        { authority :=
            { sound := by
                intro claim certificate accepted
                exact (right.projection kind).authority.sound
                  claim.down certificate.down accepted
              complete := by
                intro claim certified
                obtain ⟨certificate, accepted⟩ :=
                  (right.projection kind).authority.complete
                    claim.down certified
                exact ⟨ULift.up certificate, accepted⟩ }
          project := by
            intro claim certified
            exact (right.projection kind).project claim.down certified }

@[simp] theorem sum_left_check
    {LeftKind : Type uLeftKind} {RightKind : Type uRightKind}
    (left : AuthorityFamily.{uLeftKind, uLeftClaim, uLeftCertificate}
      LeftKind)
    (right : AuthorityFamily.{uRightKind, uRightClaim, uRightCertificate}
      RightKind)
    (kind : LeftKind) (claim : left.Claim kind)
    (certificate : left.Certificate kind) :
    ((sum left right).checker (.inl kind)).check
        (ULift.up claim) (ULift.up certificate) =
      (left.checker kind).check claim certificate :=
  rfl

@[simp] theorem sum_right_check
    {LeftKind : Type uLeftKind} {RightKind : Type uRightKind}
    (left : AuthorityFamily.{uLeftKind, uLeftClaim, uLeftCertificate}
      LeftKind)
    (right : AuthorityFamily.{uRightKind, uRightClaim, uRightCertificate}
      RightKind)
    (kind : RightKind) (claim : right.Claim kind)
    (certificate : right.Certificate kind) :
    ((sum left right).checker (.inr kind)).check
        (ULift.up claim) (ULift.up certificate) =
      (right.checker kind).check claim certificate :=
  rfl

/-- Disjointly hosting a second authority family neither enlarges nor shrinks
the exact certificate scope of a claim from the left family. -/
theorem sum_left_certified_iff_exists_accepted
    {LeftKind : Type uLeftKind} {RightKind : Type uRightKind}
    [DecidableEq LeftKind] [DecidableEq RightKind]
    (left : AuthorityFamily.{uLeftKind, uLeftClaim, uLeftCertificate}
      LeftKind)
    (right : AuthorityFamily.{uRightKind, uRightClaim, uRightCertificate}
      RightKind)
    (kind : LeftKind) (claim : left.Claim kind) :
    left.Certified kind claim <->
      exists certificate : (sum left right).PackedCertificate,
        (sum left right).packedChecker.check
          ⟨Sum.inl kind, ULift.up claim⟩ certificate = true := by
  change (sum left right).packedCertified
      (⟨Sum.inl kind, ULift.up claim⟩ : (sum left right).PackedClaim) <-> _
  exact (sum left right).packedChecker_authority.meaning_iff_exists_certificate _

/-- The same exact-scope preservation holds for claims from the right family. -/
theorem sum_right_certified_iff_exists_accepted
    {LeftKind : Type uLeftKind} {RightKind : Type uRightKind}
    [DecidableEq LeftKind] [DecidableEq RightKind]
    (left : AuthorityFamily.{uLeftKind, uLeftClaim, uLeftCertificate}
      LeftKind)
    (right : AuthorityFamily.{uRightKind, uRightClaim, uRightCertificate}
      RightKind)
    (kind : RightKind) (claim : right.Claim kind) :
    right.Certified kind claim <->
      exists certificate : (sum left right).PackedCertificate,
        (sum left right).packedChecker.check
          ⟨Sum.inr kind, ULift.up claim⟩ certificate = true := by
  change (sum left right).packedCertified
      (⟨Sum.inr kind, ULift.up claim⟩ : (sum left right).PackedClaim) <-> _
  exact (sum left right).packedChecker_authority.meaning_iff_exists_certificate _

end AuthorityFamily

/-! ## A concrete cross-tag rejection canary -/

inductive DemoKind where
  | left
  | right
deriving DecidableEq

private def demoFamily : AuthorityFamily DemoKind where
  Claim := fun _ => Bool
  Certificate := fun _ => Unit
  checker
    | .left => { check := fun claim _ => claim }
    | .right => { check := fun claim _ => !claim }
  Certified
    | .left => fun claim => claim = true
    | .right => fun claim => claim = false
  Meaning
    | .left => fun claim => claim = true
    | .right => fun claim => claim = false
  projection := by
    intro kind
    cases kind <;> exact
      { authority :=
          { sound := by intro claim _ accepted; simpa using accepted
            complete := by intro claim meaningful; exact ⟨(), by simp [meaningful]⟩ }
        project := by intro _ meaningful; exact meaningful }

theorem demo_cross_tag_rejected :
    demoFamily.packedChecker.check
      ⟨DemoKind.left, true⟩ ⟨DemoKind.right, ()⟩ = false := by
  exact demoFamily.packedChecker_rejects_wrongKind (by decide) true ()

end Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
