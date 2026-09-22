import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre
import Mettapedia.GSLT.Core.RelationPresentation

/-!
# Exact-image interpretation of revisioned occurrence flow in GSLT-IL

An arbitrary occurrence source and revision-keying policy determine the
retained Need relation.  The selected returned-command fragment of GSLT-IL
carries equivalent one-step evidence, relational chains, open derivations,
and admitted execution.  The relational interpretation uses the semantic
relation interface shared with the cumulative-tower presentation.

No candidate operational assembly is assumed.  The one universe lift at the
retained-edge relation boundary only places its proof data in the endpoint
universe; the comparison retains the actual edge through its inverse.

The result is deliberately not promoted to a universal property for the full
command language.  Commands under an authored route and the act of applying a
route lie outside the returned-fibre image.  Those counterexamples are part of
the theorem package, and the premises needed for the larger theorem remain a
machine-visible nonempty list.
-/


namespace Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage

open _root_.CategoryTheory
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow
open Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre

universe uSpace uRequest uAnswer uKey

variable {Space : Type uSpace} {Request : Type uRequest}
  {Answer : Type uAnswer} [DecidableEq Answer]

/-! ## One-step and Chain interpretation -/

/-- Retained revisioned-occurrence edges as a proof-relevant relation. -/
def occurrenceStepRel (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    Mettapedia.GSLT.RelationPresentation.Rel (Claim occurrences keying) (Claim occurrences keying) where
  evidence := fun source target =>
    ULift.{max uSpace uRequest uAnswer uKey} (Step occurrences keying source target)

/-- The corresponding relation in the selected returned GSLT-IL fibre. -/
def returnedStepRel (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    Mettapedia.GSLT.RelationPresentation.Rel (Claim occurrences keying) (Claim occurrences keying) where
  evidence := ReturnedStep occurrences keying

/-- Exact one-step interpretation.  It maps proof objects, not only endpoint
reachability propositions. -/
def stepEvidenceEquiv (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (source target : Claim occurrences keying) :
    (occurrenceStepRel occurrences keying).evidence source target ≃
      (returnedStepRel occurrences keying).evidence source target :=
  Equiv.ulift.trans (stepEquiv occurrences keying)

/-- Exact relational-Chain interpretation.  The intermediate claim and both
step witnesses survive the comparison. -/
def chainEvidenceEquiv (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (source target : Claim occurrences keying) :
    (Mettapedia.GSLT.RelationPresentation.Rel.Chain
      (occurrenceStepRel occurrences keying) (occurrenceStepRel occurrences keying)).evidence
        source target ≃
      (Mettapedia.GSLT.RelationPresentation.Rel.Chain (returnedStepRel occurrences keying)
        (returnedStepRel occurrences keying)).evidence source target where
  toFun witness :=
    ⟨witness.1, stepEvidenceEquiv occurrences keying _ _ witness.2.1,
      stepEvidenceEquiv occurrences keying _ _ witness.2.2⟩
  invFun witness :=
    ⟨witness.1, (stepEvidenceEquiv occurrences keying _ _).symm witness.2.1,
      (stepEvidenceEquiv occurrences keying _ _).symm witness.2.2⟩
  left_inv witness := by
    rcases witness with ⟨middle, earlier, later⟩
    refine Sigma.ext (β := fun middle =>
      (occurrenceStepRel occurrences keying).evidence source middle ×
        (occurrenceStepRel occurrences keying).evidence middle target) rfl ?_
    apply heq_of_eq
    exact Prod.ext ((stepEvidenceEquiv occurrences keying _ _).symm_apply_apply earlier)
      ((stepEvidenceEquiv occurrences keying _ _).symm_apply_apply later)
  right_inv witness := by
    rcases witness with ⟨middle, earlier, later⟩
    refine Sigma.ext (β := fun middle =>
      (returnedStepRel occurrences keying).evidence source middle ×
        (returnedStepRel occurrences keying).evidence middle target) rfl ?_
    apply heq_of_eq
    exact Prod.ext ((stepEvidenceEquiv occurrences keying _ _).apply_symm_apply earlier)
      ((stepEvidenceEquiv occurrences keying _ _).apply_symm_apply later)

/-! ## The exact returned image and its strict boundary -/

/-- Commands represented by the revisioned-occurrence returned-fibre encoding. -/
def InReturnedImage (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (command : Command (diagram occurrences keying)) : Prop :=
  ∃ claim : Claim occurrences keying, command = encodeClaim occurrences keying claim

theorem encodeClaim_inReturnedImage (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    InReturnedImage occurrences keying (encodeClaim occurrences keying claim) :=
  ⟨claim, rfl⟩

/-- A pending route command is a concrete command outside the exact image. -/
theorem pendingClaim_outsideReturnedImage
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    ¬ InReturnedImage occurrences keying (pendingClaim occurrences keying claim) := by
  rintro ⟨other, equal⟩
  exact pendingClaim_not_encoded occurrences keying claim other equal

/-- The `underVia` edge exists whenever the source fibre has a retained occurrence
step; neither endpoint is silently reclassified as a returned command. -/
def underIdentityVia (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying}
    (step : Step occurrences keying source target) :
    Command.Step (diagram occurrences keying) (pendingClaim occurrences keying source)
      (pendingClaim occurrences keying target) :=
  .underVia (CategoryTheory.CategoryStruct.id stage)
    (semanticStep_mk (stepToClaimStep occurrences keying step))

theorem underIdentityVia_source_outside
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying}
    (_step : Step occurrences keying source target) :
    ¬ InReturnedImage occurrences keying (pendingClaim occurrences keying source) :=
  pendingClaim_outsideReturnedImage occurrences keying source

theorem underIdentityVia_target_outside
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying}
    (_step : Step occurrences keying source target) :
    ¬ InReturnedImage occurrences keying (pendingClaim occurrences keying target) :=
  pendingClaim_outsideReturnedImage occurrences keying target

/-- Applying the route starts outside the returned image, even though its
target is a returned state after identity transport. -/
theorem applyIdentityVia_source_outside
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    ¬ InReturnedImage occurrences keying (pendingClaim occurrences keying claim) :=
  pendingClaim_outsideReturnedImage occurrences keying claim

/-! ## The proved internal-language package -/

/-- The exact-image interpretation retains the pending-command negative
boundary; it is not an equivalence with the full GSLT-IL command language. -/
structure ExactImageWitness (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) where
  oneStep : ∀ (source target : Claim occurrences keying),
    (occurrenceStepRel occurrences keying).evidence source target ≃
      (returnedStepRel occurrences keying).evidence source target
  chain : ∀ (source target : Claim occurrences keying),
    (Mettapedia.GSLT.RelationPresentation.Rel.Chain
      (occurrenceStepRel occurrences keying)
      (occurrenceStepRel occurrences keying)).evidence source target ≃
      (Mettapedia.GSLT.RelationPresentation.Rel.Chain
        (returnedStepRel occurrences keying)
        (returnedStepRel occurrences keying)).evidence source target
  openDerivations :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.CloneEquivalence
      (Clone occurrences keying) (ReturnedClone occurrences keying)
  admissionCommutes :
    ∀ (rule : Mettapedia.GSLT.LanguageDef.NIKMetalogic.OperationalRule
        (Step occurrences keying))
      (prior : (Clone occurrences keying).Hom [] rule.source),
    toReturned occurrences keying
        ((admittedRules occurrences keying).toAdmissionHom rule |>.run
          (singletonEnvironment occurrences keying prior)) =
      ((returnedAdmittedRules occurrences keying).toAdmissionHom
          (toReturnedRule occurrences keying rule) |>.run
        (returnedSingletonEnvironment occurrences keying
          (toReturned occurrences keying prior)))
  returnedPositive : ∀ (claim : Claim occurrences keying),
    InReturnedImage occurrences keying (encodeClaim occurrences keying claim)
  pendingStrict : ∀ (claim : Claim occurrences keying),
    ¬ InReturnedImage occurrences keying (pendingClaim occurrences keying claim)
  applyViaStrict : ∀ (claim : Claim occurrences keying),
    Nonempty (Command.Step (diagram occurrences keying)
      (pendingClaim occurrences keying claim)
      (.at stage (transportTerm (diagram occurrences keying)
        (CategoryTheory.CategoryStruct.id stage)
        (quoteClaim occurrences keying claim)))) ∧
      ¬ InReturnedImage occurrences keying (pendingClaim occurrences keying claim)

def exactImageWitness (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    ExactImageWitness occurrences keying where
  oneStep := stepEvidenceEquiv occurrences keying
  chain := chainEvidenceEquiv occurrences keying
  openDerivations := cloneEquivalence occurrences keying
  admissionCommutes := admission_square_commutes occurrences keying
  returnedPositive := encodeClaim_inReturnedImage occurrences keying
  pendingStrict := pendingClaim_outsideReturnedImage occurrences keying
  applyViaStrict := by
    intro claim
    exact ⟨⟨applyIdentityVia occurrences keying claim⟩,
      applyIdentityVia_source_outside occurrences keying claim⟩

/-! ## Premises still missing for the full universal property -/

/-- Named premises that separate the proved exact-image theorem from a future
full internal-language universal property. -/
inductive UniversalPropertyPremise where
  | intrinsicCommandSyntax
  | typedTransport
  | transportSubstitution
  | cellCoherence
  | initialFactorization
deriving DecidableEq, Repr

def openUniversalPropertyPremises : List UniversalPropertyPremise :=
  [.intrinsicCommandSyntax, .typedTransport, .transportSubstitution,
    .cellCoherence, .initialFactorization]

theorem openUniversalPropertyPremises_count :
    openUniversalPropertyPremises.length = 5 :=
  rfl

/-- The returned fragment cannot satisfy full-command decoding. -/
theorem returned_fragment_has_no_full_command_decode
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    ¬ ∃ decode : Command (diagram occurrences keying) → Claim occurrences keying,
      ∀ command, encodeClaim occurrences keying (decode command) = command := by
  rintro ⟨decode, rightInverse⟩
  exact pendingClaim_not_encoded occurrences keying claim
    (decode (pendingClaim occurrences keying claim))
    (rightInverse (pendingClaim occurrences keying claim)).symm

#print axioms stepEvidenceEquiv
#print axioms chainEvidenceEquiv
#print axioms exactImageWitness
#print axioms pendingClaim_outsideReturnedImage
#print axioms returned_fragment_has_no_full_command_decode
#print axioms openUniversalPropertyPremises_count

end Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage
