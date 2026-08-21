import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation
import Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalInternalLanguage

/-!
# Prime as an exact-image internal language for GSLT-IL

This module states the presently proved internal-language result at its exact
scope.  Prime's retained Need relation is interpreted as a proof-relevant
relation, and the selected returned-fibre fragment of GSLT-IL carries exactly
the same one-step witnesses, relational chains, open derivations, and admitted
execution.

The result is deliberately not promoted to a universal property for the full
command language.  Commands under an authored route and the act of applying a
route lie outside the returned-fibre image.  Those counterexamples are part of
the theorem package, and the premises needed for the larger theorem remain a
machine-visible nonempty list.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe

namespace GSLTILExactImage

open CategoryTheory
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeNeedProofFlow
open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeGSLTILReturnedFibre

/-- The live Prime operational model used by the returned-fibre theorem. -/
abbrev PrimeModel := Mettapedia.Languages.MeTTa.Prime.Language.Model

/-! ## One-step and Chain interpretation -/

/-- Prime's live retained Need steps as a proof-relevant relation. -/
def primeStepRel (model : PrimeModel) :
    RelationalInternalLanguage.Semantic.Rel (Claim model) (Claim model) where
  evidence := Step model

/-- The corresponding relation in the selected returned GSLT-IL fibre. -/
def returnedStepRel (model : PrimeModel) :
    RelationalInternalLanguage.Semantic.Rel (Claim model) (Claim model) where
  evidence := ReturnedStep model

/-- Exact one-step interpretation.  It maps proof objects, not only endpoint
reachability propositions. -/
def stepEvidenceEquiv (model : PrimeModel) (source target : Claim model) :
    (primeStepRel model).evidence source target ≃
      (returnedStepRel model).evidence source target :=
  stepEquiv model

/-- Exact relational-Chain interpretation.  The intermediate claim and both
step witnesses survive the comparison. -/
def chainEvidenceEquiv (model : PrimeModel) (source target : Claim model) :
    (RelationalInternalLanguage.Semantic.Rel.Chain
      (primeStepRel model) (primeStepRel model)).evidence
        source target ≃
      (RelationalInternalLanguage.Semantic.Rel.Chain (returnedStepRel model)
        (returnedStepRel model)).evidence source target where
  toFun witness :=
    ⟨witness.1, stepEquiv model witness.2.1,
      stepEquiv model witness.2.2⟩
  invFun witness :=
    ⟨witness.1, (stepEquiv model).symm witness.2.1,
      (stepEquiv model).symm witness.2.2⟩
  left_inv witness := by
    rcases witness with ⟨middle, earlier, later⟩
    simp
  right_inv witness := by
    rcases witness with ⟨middle, earlier, later⟩
    simp

/-! ## The exact returned image and its strict boundary -/

/-- Commands represented by the current Prime returned-fibre encoding. -/
def InReturnedImage (model : PrimeModel)
    (command : Command (diagram model)) : Prop :=
  ∃ claim : Claim model, command = encodeClaim model claim

theorem encodeClaim_inReturnedImage (model : PrimeModel) (claim : Claim model) :
    InReturnedImage model (encodeClaim model claim) :=
  ⟨claim, rfl⟩

/-- A pending route command is a concrete command outside the exact image. -/
theorem pendingClaim_outsideReturnedImage
    (model : PrimeModel) (claim : Claim model) :
    ¬ InReturnedImage model (pendingClaim model claim) := by
  rintro ⟨other, equal⟩
  exact pendingClaim_not_encoded model claim other equal

/-- The `underVia` edge exists whenever the source fibre has a retained Prime
step; neither endpoint is silently reclassified as a returned command. -/
def underIdentityVia (model : PrimeModel) {source target : Claim model}
    (step : Step model source target) :
    Command.Step (diagram model) (pendingClaim model source)
      (pendingClaim model target) :=
  .underVia (CategoryTheory.CategoryStruct.id stage)
    (semanticStep_mk (stepToClaimStep model step))

theorem underIdentityVia_source_outside
    (model : PrimeModel) {source target : Claim model}
    (_step : Step model source target) :
    ¬ InReturnedImage model (pendingClaim model source) :=
  pendingClaim_outsideReturnedImage model source

theorem underIdentityVia_target_outside
    (model : PrimeModel) {source target : Claim model}
    (_step : Step model source target) :
    ¬ InReturnedImage model (pendingClaim model target) :=
  pendingClaim_outsideReturnedImage model target

/-- Applying the route starts outside the returned image, even though its
target is a returned state after identity transport. -/
theorem applyIdentityVia_source_outside
    (model : PrimeModel) (claim : Claim model) :
    ¬ InReturnedImage model (pendingClaim model claim) :=
  pendingClaim_outsideReturnedImage model claim

/-! ## The proved internal-language package -/

/-- The exact-image internal-language theorem currently earned by Prime.
It includes the negative boundary, so an inhabitant cannot be misreported as
an equivalence with the full GSLT-IL command language. -/
structure ExactImageWitness where
  oneStep : ∀ (model : PrimeModel) (source target : Claim model),
    (primeStepRel model).evidence source target ≃
      (returnedStepRel model).evidence source target
  chain : ∀ (model : PrimeModel) (source target : Claim model),
    (RelationalInternalLanguage.Semantic.Rel.Chain
      (primeStepRel model) (primeStepRel model)).evidence
        source target ≃
      (RelationalInternalLanguage.Semantic.Rel.Chain (returnedStepRel model)
        (returnedStepRel model)).evidence source target
  openDerivations : ∀ model : PrimeModel,
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.CloneEquivalence
      (Clone model) (ReturnedClone model)
  admissionCommutes : ∀ (model : PrimeModel)
      (rule : Mettapedia.GSLT.LanguageDef.NIKMetalogic.OperationalRule
        (Step model))
      (prior : (Clone model).Hom [] rule.source),
    toReturned model
        ((admittedRules model).toAdmissionHom rule |>.run
          (singletonEnvironment model prior)) =
      ((returnedAdmittedRules model).toAdmissionHom
          (toReturnedRule model rule) |>.run
        (returnedSingletonEnvironment model (toReturned model prior)))
  returnedPositive : ∀ (model : PrimeModel) (claim : Claim model),
    InReturnedImage model (encodeClaim model claim)
  pendingStrict : ∀ (model : PrimeModel) (claim : Claim model),
    ¬ InReturnedImage model (pendingClaim model claim)
  applyViaStrict : ∀ (model : PrimeModel) (claim : Claim model),
    Nonempty (Command.Step (diagram model) (pendingClaim model claim)
      (.at stage (transportTerm (diagram model)
        (CategoryTheory.CategoryStruct.id stage) (quoteClaim model claim)))) ∧
      ¬ InReturnedImage model (pendingClaim model claim)

def exactImageWitness : ExactImageWitness where
  oneStep := stepEvidenceEquiv
  chain := chainEvidenceEquiv
  openDerivations := cloneEquivalence
  admissionCommutes := admission_square_commutes
  returnedPositive := encodeClaim_inReturnedImage
  pendingStrict := pendingClaim_outsideReturnedImage
  applyViaStrict := by
    intro model claim
    exact ⟨⟨applyIdentityVia model claim⟩,
      applyIdentityVia_source_outside model claim⟩

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

/-- The present returned fragment cannot satisfy full-command decoding. -/
theorem current_fragment_has_no_full_command_decode
    (model : PrimeModel) (claim : Claim model) :
    ¬ ∃ decode : Command (diagram model) → Claim model,
      ∀ command, encodeClaim model (decode command) = command := by
  rintro ⟨decode, rightInverse⟩
  exact pendingClaim_not_encoded model claim
    (decode (pendingClaim model claim))
    (rightInverse (pendingClaim model claim)).symm

#print axioms stepEvidenceEquiv
#print axioms chainEvidenceEquiv
#print axioms exactImageWitness
#print axioms pendingClaim_outsideReturnedImage
#print axioms current_fragment_has_no_full_command_decode
#print axioms openUniversalPropertyPremises_count

end GSLTILExactImage

end Mettapedia.Languages.MeTTa.PureKernel.Universe
