import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalComputationSoundness

/-!
# Soundness of all generated external dependent judgments

Every authored local rule is interpreted in an independently supplied CwF
with strictly stable products and sums, their local beta/eta equations, and
the actual primitive header realization. The complete generated derivation
theorem is proved by induction on its retained premise trees.

No global model soundness, syntactic classifying property or internal
universe operation is assumed. The theorem concerns this strict class of
selected dependent-model representatives.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}} {D : Signature S}

namespace ModelData

theorem rule_sound (model : ModelData S C) (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (eta : PiEta model.products stable.1) (rule : RuleCode D)
    (premises : (position : Fin rule.premises.length) → Interprets model (rule.premises.get position)) :
    Interprets model rule.conclusion := by
  cases rule with
  | contextNil => exact model.contextNil_sound
  | contextExtend context type =>
      exact model.contextExtend_sound context type (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | «variable» context index => exact model.variable_sound stable context index (premises ⟨0, by simp [RuleCode.premises]⟩)
  | typeFamily context symbol arguments =>
      exact model.family_sound realization context symbol arguments (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | primitive context symbol arguments =>
      exact model.primitive_sound realization stable context symbol arguments (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | piFormation context domain body =>
      exact model.piFormation_sound context domain body (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | sigmaFormation context domain body =>
      exact model.sigmaFormation_sound context domain body (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | lambda context domain body term =>
      exact model.lambda_sound context domain body term
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | application context domain body function argument =>
      exact model.application_sound stable context domain body function argument
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | pairIntroduction context domain body first second =>
      exact model.pairIntroduction_sound stable context domain body first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | firstProjection context domain body pair =>
      exact model.firstProjection_sound context domain body pair
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | secondProjection context domain body pair =>
      exact model.secondProjection_sound stable context domain body pair
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | sigmaElimination context domain body motive branch pair =>
      exact model.sigmaElimination_sound stable context domain body motive branch pair
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
        (premises ⟨3, by simp [RuleCode.premises]⟩) (premises ⟨4, by simp [RuleCode.premises]⟩)
  | termConversion context term first second =>
      exact model.termConversion_sound context term first second (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | substitutionNil context => exact model.substitutionNil_sound context (premises ⟨0, by simp [RuleCode.premises]⟩)
  | substitutionExtend source target type substitution term =>
      exact model.substitutionExtend_sound stable source target type substitution term
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | substitutionIdentity context => exact model.substitutionIdentity_sound context (premises ⟨0, by simp [RuleCode.premises]⟩)
  | substitutionCompose source middle target first second =>
      exact model.substitutionCompose_sound stable source middle target first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | substitutionWeaken context type => exact model.substitutionWeaken_sound context type (premises ⟨0, by simp [RuleCode.premises]⟩)
  | substituteType source target substitution type =>
      exact model.substituteType_sound stable source target substitution type
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | substituteTerm source target substitution term type =>
      exact model.substituteTerm_sound stable source target substitution term type
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | contextReflexivity context => exact model.contextReflexivity_sound context (premises ⟨0, by simp [RuleCode.premises]⟩)
  | contextSymmetry first second => exact model.contextSymmetry_sound first second (premises ⟨0, by simp [RuleCode.premises]⟩)
  | contextTransitivity first middle last =>
      exact model.contextTransitivity_sound first middle last (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | contextExtendEquality first second firstType secondType =>
      exact model.contextExtendEquality_sound first second firstType secondType
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | transportType first second type =>
      exact model.transportType_sound first second type (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | transportTerm first second term type =>
      exact model.transportTerm_sound first second term type (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | transportSubstitution source source' target target' substitution =>
      exact model.transportSubstitution_sound source source' target target' substitution
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | typeReflexivity context type => exact model.typeReflexivity_sound context type (premises ⟨0, by simp [RuleCode.premises]⟩)
  | typeSymmetry context first second => exact model.typeSymmetry_sound context first second (premises ⟨0, by simp [RuleCode.premises]⟩)
  | typeTransitivity context first middle last =>
      exact model.typeTransitivity_sound context first middle last (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | termReflexivity context term type => exact model.termReflexivity_sound context term type (premises ⟨0, by simp [RuleCode.premises]⟩)
  | termSymmetry context first second type => exact model.termSymmetry_sound context first second type (premises ⟨0, by simp [RuleCode.premises]⟩)
  | termTransitivity context first middle last type =>
      exact model.termTransitivity_sound context first middle last type (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | equalityConversion context first second firstType secondType =>
      exact model.equalityConversion_sound context first second firstType secondType
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | transportTypeEquality source target first second =>
      exact model.transportTypeEquality_sound source target first second (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | transportTermEquality source target first second type =>
      exact model.transportTermEquality_sound source target first second type (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | piCongruence context firstDomain secondDomain firstBody secondBody =>
      exact model.piCongruence_sound context firstDomain secondDomain firstBody secondBody
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | sigmaCongruence context firstDomain secondDomain firstBody secondBody =>
      exact model.sigmaCongruence_sound context firstDomain secondDomain firstBody secondBody
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | familyCongruence context symbol first second =>
      exact model.familyCongruence_sound realization context symbol first second (premises ⟨1, by simp [RuleCode.premises]⟩)
  | primitiveCongruence context symbol first second =>
      exact model.primitiveCongruence_sound realization stable context symbol first second (premises ⟨1, by simp [RuleCode.premises]⟩)
  | lambdaCongruence context domain body first second =>
      exact model.lambdaAnnotationCongruence_sound context domain domain body body first second
        (model.typeReflexivity_sound context domain (premises ⟨0, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, by simp [RuleCode.premises]⟩)) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument =>
      exact model.applicationAnnotationCongruence_sound stable context domain domain body body
        firstFunction secondFunction firstArgument secondArgument
        (model.typeReflexivity_sound context domain (premises ⟨0, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, by simp [RuleCode.premises]⟩))
        (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | pairCongruence context domain body firstLeft secondLeft firstRight secondRight =>
      exact model.pairAnnotationCongruence_sound stable context domain domain body body
        firstLeft secondLeft firstRight secondRight
        (model.typeReflexivity_sound context domain (premises ⟨0, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, by simp [RuleCode.premises]⟩))
        (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | firstCongruence context domain body first second =>
      exact model.firstAnnotationCongruence_sound context domain domain body body first second
        (model.typeReflexivity_sound context domain (premises ⟨0, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, by simp [RuleCode.premises]⟩)) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | secondCongruence context domain body first second =>
      exact model.secondAnnotationCongruence_sound stable context domain domain body body first second
        (model.typeReflexivity_sound context domain (premises ⟨0, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, by simp [RuleCode.premises]⟩)) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair =>
      exact model.sigmaEliminationAnnotationCongruence_sound stable context domain domain body body motive motive
        firstBranch secondBranch firstPair secondPair
        (model.typeReflexivity_sound context domain (premises ⟨0, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, by simp [RuleCode.premises]⟩))
        (model.typeReflexivity_sound (.snoc context (.sigma domain body)) motive (premises ⟨2, by simp [RuleCode.premises]⟩))
        (premises ⟨3, by simp [RuleCode.premises]⟩) (premises ⟨4, by simp [RuleCode.premises]⟩)
  | lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
      exact model.lambdaAnnotationCongruence_sound context firstDomain secondDomain firstBody secondBody first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody
      firstFunction secondFunction firstArgument secondArgument =>
      exact model.applicationAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody
        firstFunction secondFunction firstArgument secondArgument
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩) (premises ⟨4, by simp [RuleCode.premises]⟩)
  | pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight =>
      exact model.pairAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody
        firstLeft secondLeft firstRight secondRight
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩) (premises ⟨4, by simp [RuleCode.premises]⟩)
  | firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
      exact model.firstAnnotationCongruence_sound context firstDomain secondDomain firstBody secondBody first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
      exact model.secondAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody
      firstMotive secondMotive firstBranch secondBranch firstPair secondPair =>
      exact model.sigmaEliminationAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody
        firstMotive secondMotive firstBranch secondBranch firstPair secondPair
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
        (premises ⟨5, by simp [RuleCode.premises]⟩) (premises ⟨7, by simp [RuleCode.premises]⟩)
  | piBeta context domain body term argument =>
      exact model.piBeta_sound stable beta context domain body term argument
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | piEta context domain body function =>
      exact model.piEta_sound stable eta context domain body function
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | sigmaFirstBeta context domain body first second =>
      exact model.sigmaFirstBeta_sound stable context domain body first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | sigmaSecondBeta context domain body first second =>
      exact model.sigmaSecondBeta_sound stable context domain body first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
  | sigmaEta context domain body pair =>
      exact model.sigmaEta_sound context domain body pair
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | sigmaEliminationBeta context domain body motive branch first second =>
      exact model.sigmaEliminationBeta_sound stable context domain body motive branch first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
        (premises ⟨3, by simp [RuleCode.premises]⟩) (premises ⟨4, by simp [RuleCode.premises]⟩) (premises ⟨5, by simp [RuleCode.premises]⟩)
  | sigmaEliminationEta context domain body motive term pair =>
      exact model.sigmaEliminationEta_sound stable context domain body motive term pair
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
        (premises ⟨3, by simp [RuleCode.premises]⟩) (premises ⟨4, by simp [RuleCode.premises]⟩)
  | substituteTypeEquality source target substitution first second =>
      exact model.substituteTypeEquality_sound stable source target substitution first second
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | substituteTermEquality source target substitution first second type =>
      exact model.substituteTermEquality_sound stable source target substitution first second type
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | substitutionReflexivity source target substitution =>
      exact model.substitutionReflexivity_sound source target substitution (premises ⟨0, by simp [RuleCode.premises]⟩)
  | substitutionSymmetry source target first second =>
      exact model.substitutionSymmetry_sound source target first second (premises ⟨0, by simp [RuleCode.premises]⟩)
  | substitutionTransitivity source target first middle last =>
      exact model.substitutionTransitivity_sound source target first middle last
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | substitutionExtendEquality source target type first second firstTerm secondTerm =>
      exact model.substitutionExtendEquality_sound stable source target type first second firstTerm secondTerm
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | typeSubstitutionCongruence source target first second type =>
      exact model.typeSubstitutionCongruence_sound stable source target first second type
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | termSubstitutionCongruence source target first second term type =>
      exact model.termSubstitutionCongruence_sound stable source target first second term type
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)

end ModelData

namespace Derivation

theorem sound (model : ModelData S C) (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (eta : PiEta model.products stable.1) {judgment : Judgment S}
    (derivation : Derivation D judgment) : Interprets model judgment := by
  let algebra : JudgmentDerivation.Algebra (judgmentSignature D) := {
    Carrier := fun judgment => PLift (Interprets model judgment)
    conclude := by
      intro judgment rule premises
      rcases rule with ⟨rule, conclusion⟩
      cases conclusion
      exact ⟨model.rule_sound realization stable beta eta rule
        (fun position => (premises ⟨position⟩).down)⟩ }
  exact (JudgmentDerivation.interpret algebra derivation).down

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
