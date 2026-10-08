import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalHeaderFormation

/-!
# Soundness under earlier-declaration realization

Only primitive symbols actually occurring below a supplied declaration rank
require their header meanings to be realized. Every rule occurrence and premise
of the supplied derivation respects that bound. The theorem supplies the local
induction step used to realize ordered declarations successively; it does not
assume a global interpreter or global source roundtrip.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u c s t m
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}

structure BoundedRealization (model : ModelData S C) (D : Signature S) (bound : Nat) : Prop where
  typeHeader : ∀ symbol, D.typeRank symbol < bound →
    model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol)
  termHeader : ∀ symbol, D.termRank symbol < bound →
    model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol)
  termResult : ∀ symbol, D.termRank symbol < bound →
    model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol)

namespace ModelData

variable (model : ModelData S C) {n : Nat}

theorem family_sound_before (symbol : S.TypeSymbol)
    (headerRead : model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol))
    (context : ContextExpr S n)
    (arguments : Substitution S (S.typeArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.typeParameters symbol) arguments)) :
    Interprets model (.type context (.family symbol arguments)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases argumentsInterpreted.substitutionAt Γ (model.typeParameters symbol)
    contextRead headerRead with ⟨σ, argumentsRead⟩
  exact ⟨Γ, model.familyAt symbol σ, contextRead, model.evaluate_family Γ symbol arguments σ
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp argumentsRead)⟩

theorem primitive_sound_before (symbol : S.TermSymbol)
    (headerRead : model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol))
    (resultRead : model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol))
    (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n)
    (arguments : Substitution S (S.termArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.termParameters symbol) arguments)) :
    Interprets model (.term context (.primitive symbol arguments)
      ((D.termResult symbol).substitute arguments)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases argumentsInterpreted.substitutionAt Γ (model.termParameters symbol)
    contextRead headerRead with ⟨σ, argumentsRead⟩
  let modelMap := ModelSubstitution.ofEvaluated model Γ (model.termParameters symbol) arguments σ argumentsRead
  exact ⟨Γ, (model.primitiveAt symbol σ).1, (model.primitiveAt symbol σ).2, contextRead,
    model.evaluateType_substitute stable (D.termResult symbol) Γ (model.termParameters symbol)
      arguments modelMap _ resultRead, model.evaluate_primitive Γ symbol arguments σ modelMap.readout⟩

theorem familyCongruence_sound_before
    (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (headerRead : model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol))
    (first second : Substitution S (S.typeArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.typeParameters symbol) first second)) :
    Interprets model (.typeEq context (.family symbol first) (.family symbol second)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans headerRead)
  exact ⟨Γ, model.familyAt symbol σ, contextRead,
    model.evaluate_family Γ symbol first σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead),
    model.evaluate_family Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem primitiveCongruence_sound_before
    (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (headerRead : model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol))
    (resultRead : model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol))
    (first second : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.termParameters symbol) first second)) :
    Interprets model (.termEq context (.primitive symbol first) (.primitive symbol second)
      ((D.termResult symbol).substitute first)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans headerRead)
  let firstMap := ModelSubstitution.ofEvaluated model Γ (model.termParameters symbol) first σ firstRead
  exact ⟨Γ, (model.primitiveAt symbol σ).1, (model.primitiveAt symbol σ).2, contextRead,
    model.evaluateType_substitute stable (D.termResult symbol) Γ (model.termParameters symbol)
      first firstMap _ resultRead,
    model.evaluate_primitive Γ symbol first σ firstMap.readout,
    model.evaluate_primitive Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem rule_sound_before (model : ModelData S C) {bound : Nat}
    (realization : BoundedRealization model D bound)
    (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (eta : PiEta model.products stable.1) (rule : RuleCode D)
    (ordered : rule.conclusion.before D bound)
    (premises : (position : Fin rule.premises.length) → Interprets model (rule.premises.get position)) :
    Interprets model rule.conclusion := by
  cases rule with
  | contextNil => exact model.contextNil_sound
  | contextExtend context type =>
      exact model.contextExtend_sound context type (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨1, by simp [RuleCode.premises]⟩)
  | «variable» context index => exact model.variable_sound stable context index (premises ⟨0, by simp [RuleCode.premises]⟩)
  | typeFamily context symbol arguments =>
      have earlier : D.typeRank symbol < bound := ordered.2.1
      exact model.family_sound_before symbol (realization.typeHeader symbol earlier) context arguments
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | primitive context symbol arguments =>
      have earlier : D.termRank symbol < bound := ordered.2.1.1
      exact model.primitive_sound_before symbol (realization.termHeader symbol earlier)
        (realization.termResult symbol earlier) stable context arguments
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨3, by simp [RuleCode.premises]⟩)
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
      have earlier : D.typeRank symbol < bound := ordered.2.1.1
      exact model.familyCongruence_sound_before context symbol (realization.typeHeader symbol earlier) first second (premises ⟨1, by simp [RuleCode.premises]⟩)
  | primitiveCongruence context symbol first second =>
      have earlier : D.termRank symbol < bound := ordered.2.1.1
      exact model.primitiveCongruence_sound_before stable context symbol
        (realization.termHeader symbol earlier) (realization.termResult symbol earlier) first second (premises ⟨1, by simp [RuleCode.premises]⟩)
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

theorem sound_before (model : ModelData S C) {bound : Nat}
    (realization : BoundedRealization model D bound)
    (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (eta : PiEta model.products stable.1) {judgment : Judgment S}
    (derivation : Derivation D judgment) (ordered : derivation.before bound) :
    Interprets model judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment tree => Derivation.before (D := D) bound tree → Interprets model judgment)
    (fun rule premises ih => ?_) derivation ordered
  rcases rule with ⟨rule, rfl⟩
  intro bounded
  exact model.rule_sound_before realization stable beta eta rule bounded.1
    (fun position => ih ⟨position⟩ (bounded.2 ⟨position⟩))

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
