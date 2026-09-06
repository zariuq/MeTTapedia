import Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary
import Mettapedia.GSLT.LanguageDef.InstitutionConsequence
import Mettapedia.Logic.InstitutionCanary

/-!
# Proof-sensitive canary for certified biform routes

The same biform identity route admits two exact certificate translations for
a tagged Boolean proof calculus: one retains the Boolean proof tag and one
flips it.  Both make checker replay commute because the checker validates the
native conclusion, not the tag.  The biform projection therefore identifies
the routes, while the certified-theory projection separates them.

This is a concrete boundary between event meaning and kernel proof identity.
A biform route cannot manufacture its certificate translation; qualification
must carry that translation as additional checked data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformCertificateBoundaryCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget
open Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary
open Mettapedia.GSLT.LanguageDef.CertifiedBiformTheory
open Mettapedia.GSLT.LanguageDef.InstitutionConsequence
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Logic.InstitutionCanary

/-! ## A small proof-relevant biform theory over Boolean sentences -/

abbrev boolConsequence :=
  consequenceProjection
    (Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier)

def boolLogical : PiInstitution.TheoryObject boolConsequence :=
  PiInstitution.generatedTheory boolConsequence
    (CategoryTheory.Discrete.mk ()) {true}

/-- A one-state machine with two distinct retained occurrences of its loop. -/
def loopTheory : GSLT where
  Term := Unit
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro source source' target equivalent step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    exact step

def loopEvidence : StepEvidence loopTheory where
  Evidence := fun _ _ => Bool
  erases_iff := by
    intro source target
    constructor
    · intro evidence
      trivial
    · intro step
      exact ⟨false⟩

def loopAlgorithm : ProofRelevantGSLT :=
  ⟨loopTheory, loopEvidence⟩

def boolBiform : BiformTheory boolConsequence where
  logical := boolLogical
  algorithm := loopAlgorithm
  meaning := fun _ => true
  meaning_sound := by
    intro event
    exact PiInstitution.derives_of_mem boolConsequence
      (CategoryTheory.Discrete.mk ()) (Set.mem_singleton true)

abbrev taggedCalculus :=
  PiInstitution.ProofCalculus.tagged boolConsequence

abbrev TaggedCertificate := taggedCalculus.proof.obj boolLogical

/-- Read the theorem conclusion carried by a tagged certificate.  Naming this
projection fixes the selected Boolean sentence carrier at the API boundary. -/
def taggedConclusion (certificate : TaggedCertificate) : Bool :=
  certificate.1.1

/-- Replay checks the native theorem conclusion.  The Boolean proof tag stays
available to intensional consumers but does not affect theoremhood. -/
def taggedChecker : Checker Bool TaggedCertificate where
  check formula certificate :=
    decide (taggedConclusion certificate = formula)

/-- The checker fibre is definitionally the tagged calculus proof fibre, so
the certificate boundary retains both proof occurrences exactly. -/
def taggedProofAuthority :
    ProofCarryingAuthority (taggedDiscipline boolLogical) where
  Certificate := fun _ => TaggedCertificate
  checker := fun _ => taggedChecker
  certificateBoundary := fun _ =>
    { fibreEquiv := fun formula =>
        { toFun := fun accepted =>
            ⟨accepted.1, by
              have acceptedConclusion :
                  taggedConclusion accepted.1 = formula := by
                exact of_decide_eq_true accepted.2
              exact acceptedConclusion⟩
          invFun := fun native =>
            ⟨native.1, by
              have nativeConclusion :
                  taggedConclusion native.1 = formula := by
                exact native.2
              exact decide_eq_true nativeConclusion⟩
          left_inv := by
            intro accepted
            apply Subtype.ext
            rfl
          right_inv := by
            intro native
            apply Subtype.ext
            rfl } }

def targetAuthority :
    CertificateBoundary boolBiform taggedCalculus where
  contract := taggedProofAuthority

def qualifiedTarget :
    CertifiedBiformTheory.Object taggedCalculus where
  biform := boolBiform
  boundary := targetAuthority

/-- Flip only the retained proof tag. -/
def flipCertificate (certificate : TaggedCertificate) : TaggedCertificate :=
  (certificate.1, !certificate.2)

/-- The certificate-preserving qualified identity. -/
def retainRoute : qualifiedTarget ⟶ qualifiedTarget :=
  CertifiedBiformTheory.Hom.identity qualifiedTarget

/-- A second qualified route with the same biform component and a different,
still exact, certificate action. -/
def flipRoute : qualifiedTarget ⟶ qualifiedTarget where
  biform := BiformTheory.Hom.identity boolBiform
  mapCertificate := flipCertificate
  check_commutes := by
    intro formula certificate
    rfl

/-- Positive control: the tag-flipping route still preserves exact replay. -/
theorem flipRoute_replay_commutes
    (formula : Bool)
    (certificate : TaggedCertificate) :
    taggedChecker.check formula (flipCertificate certificate) =
      taggedChecker.check formula certificate :=
  flipRoute.check_commutes formula certificate

/-- The two routes become equal after forgetting certificate transport. -/
theorem biform_images_equal :
    CertifiedBiformTheory.biformProjection.map retainRoute =
      CertifiedBiformTheory.biformProjection.map flipRoute :=
  rfl

theorem trueTheorem : true ∈ boolLogical.theory.1 :=
  PiInstitution.derives_of_mem boolConsequence
    (CategoryTheory.Discrete.mk ()) (Set.mem_singleton true)

def falseCertificate : TaggedCertificate :=
  (⟨true, trueTheorem⟩, false)

/-- The certified-theory projection still observes the changed proof occurrence. -/
theorem authority_images_distinct :
    CertifiedBiformTheory.certifiedTheoryProjection.map retainRoute ≠
      CertifiedBiformTheory.certifiedTheoryProjection.map flipRoute := by
  intro equalRoutes
  have equalCertificates := congrArg
    (fun route : qualifiedTarget.toCertifiedTheory ⟶
        qualifiedTarget.toCertifiedTheory =>
      route.mapCertificate () falseCertificate)
    equalRoutes
  have equalTags := congrArg (fun certificate => certificate.2)
    equalCertificates
  change false = true at equalTags
  exact Bool.false_ne_true equalTags

/-- Negative control: a biform route does not determine its certificate
translation. -/
theorem biform_projection_not_injective :
    ¬Function.Injective
      (fun route : qualifiedTarget ⟶ qualifiedTarget =>
        CertifiedBiformTheory.biformProjection.map route) := by
  intro injective
  exact authority_images_distinct
    (congrArg CertifiedBiformTheory.certifiedTheoryProjection.map
      (injective biform_images_equal))

#print axioms taggedProofAuthority
#print axioms flipRoute_replay_commutes
#print axioms biform_images_equal
#print axioms authority_images_distinct
#print axioms biform_projection_not_injective

end Mettapedia.GSLT.LanguageDef.BiformCertificateBoundaryCanary
