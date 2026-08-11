import Foundation.Modal.Kripke.Logic.K
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

/-!
# Intrinsic Foundation proof authorities for NIK

Foundation proof terms provide a useful Stage-0 semantic authority: a
certificate contains an intrinsically typed proof and the checker verifies
that its conclusion is the submitted claim.  This gives exact provability,
and Foundation soundness/completeness transports it to model semantics.

This is not yet an untrusted native wire format.  A Prime ProofGSLT authority
must separately provide a faithful codec or proof-term presentation and prove
that native replay refines the same checker meaning.  Keeping the intrinsic
authority explicit prevents the future serialization layer from becoming its
own semantic oracle.
-/

namespace Mettapedia.Logic.Bridges.FoundationNIKAuthority

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

universe uSystem uFormula uModel

/-! ## Generic intrinsically typed certificates -/

/-- A Foundation proof packaged with its dependent conclusion. -/
structure IntrinsicCertificate
    {System : Type uSystem} {Formula : Type uFormula}
    [LO.Entailment System Formula] (system : System) where
  conclusion : Formula
  proof : LO.Entailment.Prf system conclusion

namespace IntrinsicCertificate

variable {System : Type uSystem} {Formula : Type uFormula}
    [LO.Entailment System Formula] [DecidableEq Formula]
    (system : System)

/-- Replay checks only the exposed conclusion; proof well-typedness is carried
intrinsically by the Stage-0 certificate type. -/
def checker : Checker Formula (IntrinsicCertificate system) where
  check claim certificate := decide (certificate.conclusion = claim)

/-- Intrinsic replay is exact for Foundation provability. -/
theorem checker_authority :
    (checker system).Authority (LO.Entailment.Provable system) where
  sound := by
    intro claim certificate accepted
    have sameConclusion : certificate.conclusion = claim :=
      of_decide_eq_true accepted
    exact ⟨LO.Entailment.cast sameConclusion certificate.proof⟩
  complete := by
    rintro claim ⟨proof⟩
    exact ⟨⟨claim, proof⟩, by simp [checker]⟩

/-- With Foundation soundness, exact provability projects soundly into an
independently defined semantic model or model class. -/
def semanticProjection
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] :
    (checker system).AuthorityProjection
      (LO.Entailment.Provable system)
      (fun formula => LO.Semantics.Models model formula) where
  authority := checker_authority system
  project := by
    intro formula provable
    exact LO.Sound.sound provable

/-- Foundation completeness upgrades the semantic projection to exact
certificate authority for the selected model or model class. -/
def semanticAuthority
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    (checker system).Authority
      (fun formula => LO.Semantics.Models model formula) where
  sound := (semanticProjection system model).sound
  complete := by
    intro formula valid
    exact (checker_authority system).complete formula
      (LO.Complete.complete valid)

/-- A one-fibre NIK family exact for the selected Foundation semantics.  More
guest authorities join it through the ordinary indexed-family construction. -/
def semanticFamily
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    AuthorityFamily Unit where
  Claim := fun _ => Formula
  Certificate := fun _ => IntrinsicCertificate system
  checker := fun _ => checker system
  Certified := fun _ formula => LO.Semantics.Models model formula
  Meaning := fun _ formula => LO.Semantics.Models model formula
  projection := fun _ => (semanticAuthority system model).toProjection

end IntrinsicCertificate

/-! ## Modal K: the spatial/behavioral base guest -/

namespace ModalK

abbrev Formula := LO.Modal.Formula ℕ

abbrev Certificate :=
  IntrinsicCertificate (Formula := Formula) LO.Modal.K

def checker : Checker Formula Certificate :=
  IntrinsicCertificate.checker LO.Modal.K

/-- Exact NIK certificate authority for validity on all Kripke frames. -/
def kripkeAuthority :
    checker.Authority
      (fun formula =>
        LO.Semantics.Models LO.Modal.Kripke.FrameClass.K formula) :=
  IntrinsicCertificate.semanticAuthority
    LO.Modal.K LO.Modal.Kripke.FrameClass.K

/-- The same calculus is exact for validity on finite Kripke frames by
Foundation's filtration theorem. -/
def finiteKripkeAuthority :
    checker.Authority
      (fun formula =>
        LO.Semantics.Models LO.Modal.Kripke.FrameClass.finite_K formula) :=
  IntrinsicCertificate.semanticAuthority
    LO.Modal.K LO.Modal.Kripke.FrameClass.finite_K

/-- Modal K as one ordinary authority fibre of the default open NIK. -/
def family : AuthorityFamily Unit :=
  IntrinsicCertificate.semanticFamily
    LO.Modal.K LO.Modal.Kripke.FrameClass.K

/-- The typed semantic frontend used beneath any future Prime wire codec. -/
def frontend : Frontend family (TypedSubmission family) :=
  Frontend.typed family

/-! ### Positive and negative adapter canaries -/

def tautology : Formula :=
  LO.Axioms.ImplyK (.atom 0) (.atom 1)

def boxedTautology : Formula := □tautology

def boxedTautologyProof : LO.Entailment.Prf LO.Modal.K boxedTautology :=
  ⟨LO.Modal.Hilbert.Normal.nec
    (LO.Modal.Hilbert.Normal.implyK (.atom 0) (.atom 1))⟩

def boxedTautologyCertificate : Certificate :=
  ⟨boxedTautology, boxedTautologyProof⟩

def acceptedSubmission : TypedSubmission family :=
  ⟨(), boxedTautology, boxedTautologyCertificate⟩

def boxedClaim : family.PackedClaim :=
  ⟨(), boxedTautology⟩

theorem boxed_tautology_accepted :
    frontend.run acceptedSubmission = .accepted boxedClaim := by
  apply frontend.run_of_check_true
      (parsed := acceptedSubmission) (submission := acceptedSubmission)
  · rfl
  · rfl
  · rfl

/-- Accepted K evidence projects through Foundation soundness to validity on
all Kripke frames. -/
theorem boxed_tautology_valid_on_all_frames :
    family.packedMeaning boxedClaim :=
  frontend.accepted_implies_meaning boxed_tautology_accepted

def mismatchedSubmission : TypedSubmission family :=
  ⟨(), (.atom 0 : Formula), boxedTautologyCertificate⟩

def atomClaim : family.PackedClaim :=
  ⟨(), (.atom 0 : Formula)⟩

/-- A genuine proof certificate cannot be relabeled with another conclusion. -/
theorem mismatched_conclusion_rejected :
    frontend.run mismatchedSubmission = .rejected atomClaim := by
  apply frontend.run_of_check_false
      (parsed := mismatchedSubmission) (submission := mismatchedSubmission)
  · rfl
  · rfl
  · rfl

end ModalK

end Mettapedia.Logic.Bridges.FoundationNIKAuthority
