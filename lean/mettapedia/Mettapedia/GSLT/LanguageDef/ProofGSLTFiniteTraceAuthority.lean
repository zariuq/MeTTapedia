import Mettapedia.GSLT.LanguageDef.ProofGSLTJudgmentAuthority
import Mettapedia.OSLF.Framework.OSLFProofGSLTAuthority

/-!
# Finite OSLF traces from locally checked ProofGSLT judgments

The direct-trace generator is one convenient way to obtain local `Step`
judgments from a syntactic `LanguageDef`; it is not the boundary of finite
trace auditability.  The actual boundary is local evidence: for every edge in
the trace, some named authority must check evidence whose proved meaning is
the one-step relation of the admitted GSLT.

This module constructs the free finite trace authority over any such local
edge authority.  The local certificate may be a closed ProofGSLT article, an
open article closed by query/capability/decomposition receipts, or another
native representation that lowers to the same authority.  Cycles in the
transition graph require no special treatment for finite traces.  Claims about
an infinite execution remain separate and require a guarded cyclic or
automata-theoretic authority.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.OSLFProofGSLTAuthority

universe uAuthority uCertificate uNative uPremiseCertificate

/-! ## OSLF-generated local step judgments -/

/-- One exact edge claim in an admitted GSLT. -/
structure StepClaim (theory : GSLT) where
  source : theory.Term
  target : theory.Term

/-- The semantic meaning of a local step claim is exactly the GSLT reduction
edge, equivalently the OSLF diamond of the singleton target predicate. -/
def StepClaim.Meaning {theory : GSLT} (claim : StepClaim theory) : Prop :=
  theory.Step claim.source claim.target

/-- Local step meaning is precisely the exact-target instance of the
OSLF-generated diamond modality. -/
theorem StepClaim.meaning_iff_oslfDiamond {theory : GSLT}
    (claim : StepClaim theory) :
    claim.Meaning ↔
      gsltDiamond theory (fun candidate => candidate = claim.target)
        claim.source := by
  exact (gsltDiamond_singleton_iff_step theory claim.source claim.target).symm

/-- Regard an operational edge claim as the corresponding rich OSLF native
inhabitation judgment. -/
def StepClaim.toNativeClaim {theory : GSLT} (claim : StepClaim theory) :
    NativeClaim (gsltOSLF theory) :=
  exactStepNativeClaim theory claim.source claim.target

/-- Operational edge meaning and the rich native judgment meaning coincide.
This is the semantic bridge used by both local replay and finite traces. -/
theorem StepClaim.meaning_iff_nativeClaim {theory : GSLT}
    (claim : StepClaim theory) :
    claim.Meaning ↔ claim.toNativeClaim.Meaning := by
  exact (exactStepNativeClaim_meaning_iff_step
    theory claim.source claim.target).symm

/-- A local executable checker whose every acceptance denotes a real edge of
the admitted GSLT. -/
structure StepAuthority (AuthorityId : Type uAuthority) (theory : GSLT) where
  id : AuthorityId
  Certificate : Type uCertificate
  check : StepClaim theory → Certificate → Bool
  sound : ∀ {claim certificate}, check claim certificate = true →
    claim.Meaning

/-- A local step authority is an ordinary semantic authority with the
OSLF-generated edge meaning fixed, rather than caller-selectable. -/
def StepAuthority.toSemanticAuthority {AuthorityId : Type uAuthority}
    {theory : GSLT} (authority : StepAuthority AuthorityId theory) :
    SemanticAuthority AuthorityId (StepClaim theory) where
  id := authority.id
  Certificate := authority.Certificate
  check := authority.check
  Meaning := StepClaim.Meaning
  sound := authority.sound

/-- Completeness is deliberately separate from trusted replay. -/
def StepAuthority.Complete {AuthorityId : Type uAuthority} {theory : GSLT}
    (authority : StepAuthority AuthorityId theory) : Prop :=
  ∀ claim, claim.Meaning →
    ∃ certificate, authority.check claim certificate = true

/-- A ProofGSLT presentation sound for exact GSLT edges. -/
abbrev StepPresentationAdequacy (theory : GSLT)
    (presentation : ValidatedPresentation) :=
  JudgmentPresentationAdequacy (StepClaim theory) StepClaim.Meaning presentation

/-- A two-sided ProofGSLT presentation of exact GSLT edges. -/
abbrev ExactStepPresentation (theory : GSLT)
    (presentation : ValidatedPresentation) :=
  ExactJudgmentPresentation (StepClaim theory) StepClaim.Meaning presentation

/-- The ordinary ProofGSLT wire checker becomes a local OSLF edge authority
once its edge adequacy theorem is supplied. -/
def wireStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    {presentation : ValidatedPresentation}
    (adequacy : StepPresentationAdequacy theory presentation) :
    StepAuthority AuthorityId theory where
  id := authorityId
  Certificate := WireArticle
  check := (judgmentWireAuthority authorityId adequacy).check
  sound := (judgmentWireAuthority authorityId adequacy).sound

/-- An exact local-step presentation supplies both soundness and certificate
completeness for the ordinary versioned ProofGSLT article checker. -/
def exactWireStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    {presentation : ValidatedPresentation}
    (adequacy : ExactStepPresentation theory presentation) :
    StepAuthority AuthorityId theory :=
  wireStepAuthority authorityId adequacy.toJudgmentPresentationAdequacy

/-- Two-sided presentation adequacy is exactly the missing hypothesis needed
to make local ProofGSLT article replay complete for every real GSLT edge. -/
theorem exactWireStepAuthority_complete {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    {presentation : ValidatedPresentation}
    (adequacy : ExactStepPresentation theory presentation) :
    (exactWireStepAuthority authorityId adequacy).Complete := by
  intro claim meaningful
  exact (judgmentWireAuthority_correspondence authorityId adequacy claim).2
    meaningful

/-- An open ProofGSLT presentation sound for exact GSLT edges. -/
abbrev OpenStepPresentationAdequacy (theory : GSLT)
    (presentation : ValidatedPresentation) :=
  OpenJudgmentPresentationAdequacy
    (StepClaim theory) StepClaim.Meaning presentation

/-- Query rows, collection decompositions, binder/substitution facts, and
capability receipts close an open local edge only through their separately
sound discharger. -/
def dischargedOpenWireStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    {presentation : ValidatedPresentation}
    (adequacy : OpenStepPresentationAdequacy theory presentation)
    (discharger : PremiseDischarger.{uPremiseCertificate}
      adequacy.premiseMeaning) : StepAuthority AuthorityId theory where
  id := authorityId
  Certificate := DischargedOpenEvidence discharger.Certificate
  check := (dischargedOpenWireAuthority authorityId adequacy discharger).check
  sound := (dischargedOpenWireAuthority authorityId adequacy discharger).sound

/-! ## Free finite trace closure -/

/-- A finite trace authority is identified by the local edge authority from
which it was generated. -/
structure FiniteTraceAuthorityId (AuthorityId : Type uAuthority) where
  stepAuthority : AuthorityId
deriving Repr, DecidableEq

/-- One serialized link retains its target and the local evidence for the
edge from the previous link's target. -/
structure TraceLink (theory : GSLT) (StepCertificate : Type uCertificate) where
  target : theory.Term
  evidence : StepCertificate

/-- A finite chronological trace.  Its source and final target are stored in
the checked claim, so the evidence stores only the linked successor sequence. -/
structure TraceCertificate (theory : GSLT)
    (StepCertificate : Type uCertificate) where
  links : List (TraceLink theory StepCertificate)

/-- A finite reachability claim in one admitted GSLT. -/
structure TraceClaim (theory : GSLT) where
  source : theory.Term
  target : theory.Term

/-- Trace meaning is the GSLT's reflexive-transitive reduction, not the
behavior of a particular producer or scheduler. -/
def TraceClaim.Meaning {theory : GSLT} (claim : TraceClaim theory) : Prop :=
  theory.MultiStep claim.source claim.target

/-- Thread the current term through a chronological list of locally checked
edges and require its final value to equal the claimed target. -/
def checkTraceFrom {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term] (stepAuthority : StepAuthority AuthorityId theory)
    (final current : theory.Term) :
    List (TraceLink theory stepAuthority.Certificate) → Bool
  | [] => decide (current = final)
  | link :: links =>
      stepAuthority.check ⟨current, link.target⟩ link.evidence &&
        checkTraceFrom stepAuthority final link.target links

/-- Every accepted linked trace denotes a genuine finite GSLT reduction. -/
theorem checkTraceFrom_sound {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term] (stepAuthority : StepAuthority AuthorityId theory)
    {final current : theory.Term}
    {links : List (TraceLink theory stepAuthority.Certificate)}
    (accepted : checkTraceFrom stepAuthority final current links = true) :
    theory.MultiStep current final := by
  induction links generalizing current with
  | nil =>
      simp only [checkTraceFrom] at accepted
      have equal : current = final := of_decide_eq_true accepted
      simpa only [equal] using (GSLT.MultiStep.refl (S := theory) current)
  | cons link links inductionHypothesis =>
      simp only [checkTraceFrom, Bool.and_eq_true] at accepted
      exact .step (stepAuthority.sound accepted.1)
        (inductionHypothesis accepted.2)

/-- Generate the semantic authority for finite traces from the local OSLF
edge authority. -/
def finiteTraceAuthority {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority AuthorityId theory) :
    SemanticAuthority (FiniteTraceAuthorityId AuthorityId) (TraceClaim theory)
    where
  id := ⟨stepAuthority.id⟩
  Certificate := TraceCertificate theory stepAuthority.Certificate
  check := fun claim certificate =>
    checkTraceFrom stepAuthority claim.target claim.source certificate.links
  Meaning := TraceClaim.Meaning
  sound := by
    intro claim certificate accepted
    exact checkTraceFrom_sound stepAuthority accepted

/-- If every real local edge has checkable evidence, every finite reduction
has a checkable linked trace. -/
theorem checkTraceFrom_complete {AuthorityId : Type uAuthority}
    {theory : GSLT} [DecidableEq theory.Term]
    (stepAuthority : StepAuthority AuthorityId theory)
    (complete : stepAuthority.Complete)
    {source target : theory.Term} (trace : theory.MultiStep source target) :
    ∃ links : List (TraceLink theory stepAuthority.Certificate),
      checkTraceFrom stepAuthority target source links = true := by
  induction trace with
  | refl term =>
      exact ⟨[], by simp [checkTraceFrom]⟩
  | @step source middle target edge rest inductionHypothesis =>
      obtain ⟨edgeEvidence, edgeAccepted⟩ :=
        complete ⟨source, middle⟩ edge
      obtain ⟨links, linksAccepted⟩ := inductionHypothesis
      exact ⟨⟨middle, edgeEvidence⟩ :: links, by
        simp [checkTraceFrom, edgeAccepted, linksAccepted]⟩

/-- With local completeness, accepted finite trace existence is exactly GSLT
reachability. -/
theorem finiteTraceAuthority_correspondence
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority AuthorityId theory)
    (complete : stepAuthority.Complete) (claim : TraceClaim theory) :
    (∃ certificate : (finiteTraceAuthority stepAuthority).Certificate,
        (finiteTraceAuthority stepAuthority).check claim certificate = true) ↔
      claim.Meaning := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact (finiteTraceAuthority stepAuthority).sound accepted
  · intro meaningful
    obtain ⟨links, accepted⟩ :=
      checkTraceFrom_complete stepAuthority complete meaningful
    exact ⟨⟨links⟩, accepted⟩

/-- The native NIK obligation for a finite GSLT trace: every native
acceptance lowers to the generated trace authority. -/
abbrev FiniteTraceCheckedLowering
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority AuthorityId theory)
    (NativeEvidence : Type uNative) :=
  CheckedLowering (finiteTraceAuthority stepAuthority) NativeEvidence

/-- Native acceptance entails genuine GSLT reachability solely through
replay at the finite trace authority. -/
theorem FiniteTraceCheckedLowering.reaches
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    {stepAuthority : StepAuthority AuthorityId theory}
    {NativeEvidence : Type uNative}
    (lowering : FiniteTraceCheckedLowering stepAuthority NativeEvidence)
    {claim : TraceClaim theory} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true) :
    theory.MultiStep claim.source claim.target :=
  lowering.sound accepted

end Mettapedia.GSLT.LanguageDef.ProofGSLT
