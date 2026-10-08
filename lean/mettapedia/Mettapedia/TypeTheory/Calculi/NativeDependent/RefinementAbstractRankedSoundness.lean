import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-!
# Generated soundness below a declaration rank

A supplied proof tree uses only symbols below its bound. Only those local
primitive header and result meanings need to be realized. All dependent,
logical and guarded-assumption rules construct their interpretations from
actual local premises, including the full pair-context sum motive. This is
used to realize independently formed declarations successively; it assumes
neither a complete source interpreter nor a global source roundtrip.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C} {D : Signature S}

structure BoundedRealization (model : ModelData S C localModel) (D : Signature S)
    (bound : Nat) : Prop where
  typeHeader : ∀ symbol, D.typeRank symbol < bound →
    model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol)
  termHeader : ∀ symbol, D.termRank symbol < bound →
    model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol)
  predicateHeader : ∀ symbol, D.predicateRank symbol < bound →
    model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol)
  termResult : ∀ symbol, D.termRank symbol < bound →
    model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol)

namespace ModelData

variable (model : ModelData S C localModel) {n : Nat}

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
    (header : model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol))
    (result : model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol))
    (stable : StrictPiSubstitution localModel.products) (context : ContextExpr S n)
    (arguments : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitution context (D.termParameters symbol) arguments)) :
    Interprets model (.term context (.primitive symbol arguments)
      ((D.termResult symbol).substitute arguments)) := by
  rcases argumentsInterpreted with ⟨Γ, Δ, σ, contextRead, headerRead, argumentsRead⟩
  cases Option.some.inj (headerRead.symm.trans header)
  have resultRead := model.evaluateType_substitute stable (D.termResult symbol)
    Γ (model.termParameters symbol) arguments
      (ModelSubstitution.ofEvaluated model Γ (model.termParameters symbol) arguments σ argumentsRead)
        (model.termType symbol) result
  refine ⟨Γ, (model.primitiveAt symbol σ).1, (model.primitiveAt symbol σ).2,
    contextRead, resultRead, ?_⟩
  exact model.evaluate_primitive Γ symbol arguments σ
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp argumentsRead)

theorem familyCongruence_sound_before (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (header : model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol))
    (first second : Substitution S (S.typeArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.typeParameters symbol) first second)) :
    Interprets model (.typeEq context (.family symbol first) (.family symbol second)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans header)
  exact ⟨Γ, model.familyAt symbol σ, contextRead,
    model.evaluate_family Γ symbol first σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead),
    model.evaluate_family Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩


theorem primitiveCongruence_sound_before (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (header : model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol))
    (result : model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol))
    (first second : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.termParameters symbol) first second)) :
    Interprets model (.termEq context (.primitive symbol first) (.primitive symbol second)
      ((D.termResult symbol).substitute first)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans header)
  let firstMap := ModelSubstitution.ofEvaluated model Γ (model.termParameters symbol) first σ firstRead
  exact ⟨Γ, (model.primitiveAt symbol σ).1, (model.primitiveAt symbol σ).2, contextRead,
    model.evaluateType_substitute stable (D.termResult symbol) Γ (model.termParameters symbol)
      first firstMap _ result,
    model.evaluate_primitive Γ symbol first σ firstMap.readout,
    model.evaluate_primitive Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩


theorem predicatePrimitive_sound_before (symbol : S.PredicateSymbol)
    (header : model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol))
    (context : ContextExpr S n)
    (arguments : Substitution S (S.predicateArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.predicateParameters symbol) arguments)) :
    Interprets model (.predicate context (.atom symbol arguments)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases argumentsInterpreted.substitutionAt Γ (model.predicateParameters symbol)
    contextRead header with ⟨σ, argumentsRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_predicateAtom Γ symbol arguments σ
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp argumentsRead)⟩

theorem predicatePrimitiveCongruence_sound_before (context : ContextExpr S n) (symbol : S.PredicateSymbol)
    (header : model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol))
    (first second : Substitution S (S.predicateArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitutionEq context (D.predicateParameters symbol) first second)) :
    Interprets model (.predicateEq context (.atom symbol first) (.atom symbol second)) := by
  rcases argumentsInterpreted with ⟨Γ, Δ, σ, contextRead, headerRead, firstRead, secondRead⟩
  cases Option.some.inj (headerRead.symm.trans header)
  exact ⟨Γ, _, contextRead,
    model.evaluate_predicateAtom Γ symbol first σ
      ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead),
    model.evaluate_predicateAtom Γ symbol second σ
      ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem rule_sound_before (model : ModelData S C localModel) {bound : Nat}
    (realization : BoundedRealization model D bound)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) (rule : RuleCode D)
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
        (premises ⟨3, by simp [RuleCode.premises]⟩)
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
      exact model.familyCongruence_sound_before context symbol
        (realization.typeHeader symbol earlier) first second
        (premises ⟨1, by simp [RuleCode.premises]⟩)
  | primitiveCongruence context symbol first second =>
      have earlier : D.termRank symbol < bound := ordered.2.1.1
      exact model.primitiveCongruence_sound_before stable context symbol
        (realization.termHeader symbol earlier) (realization.termResult symbol earlier) first second
        (premises ⟨1, by simp [RuleCode.premises]⟩)
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

  | contextAssume context predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.contextAssume_sound context predicate
      all_goals assumption
  | propositionType context =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.propositionType_sound context
      all_goals assumption
  | predicatePrimitive context symbol arguments =>
      have earlier : D.predicateRank symbol < bound := ordered.2.1
      exact model.predicatePrimitive_sound_before symbol
        (realization.predicateHeader symbol earlier) context arguments
        (premises ⟨0, by simp [RuleCode.premises]⟩) (premises ⟨2, by simp [RuleCode.premises]⟩)
  | truthFormation context =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.truthFormation_sound context
      all_goals assumption
  | falsehoodFormation context =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.falsehoodFormation_sound context
      all_goals assumption
  | conjunctionFormation context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.conjunctionFormation_sound context first second
      all_goals assumption
  | disjunctionFormation context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.disjunctionFormation_sound context first second
      all_goals assumption
  | implicationFormation context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.implicationFormation_sound context first second
      all_goals assumption
  | universalFormation context domain predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.universalFormation_sound context domain predicate
      all_goals assumption
  | existentialFormation context domain predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.existentialFormation_sound context domain predicate
      all_goals assumption
  | holdsFormation context term =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.holdsFormation_sound context term
      all_goals assumption
  | imageFormation context type =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.imageFormation_sound context type
      all_goals assumption
  | quote context predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.quote_sound context predicate
      all_goals assumption
  | comprehensionFormation context domain predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.comprehensionFormation_sound context domain predicate
      all_goals assumption
  | comprehensionIntroduction context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.comprehensionIntroduction_sound stable context domain predicate value
      all_goals assumption
  | comprehensionElimination context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.comprehensionElimination_sound context domain predicate value
      all_goals assumption
  | comprehensionGuard context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.comprehensionGuard_sound stable context domain predicate value
      all_goals assumption
  | comprehensionBeta context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.comprehensionBeta_sound stable context domain predicate value
      all_goals assumption
  | comprehensionEta context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.comprehensionEta_sound context domain predicate value
      all_goals assumption
  | quoteHolds context term =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.quoteHolds_sound context term
      all_goals assumption
  | holdsQuote context predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.holdsQuote_sound context predicate
      all_goals assumption
  | hypothesis context predicate member =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.hypothesis_sound stable context predicate member
      all_goals assumption
  | truthIntroduction context =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.truthIntroduction_sound context
      all_goals assumption
  | falsehoodElimination context predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.falsehoodElimination_sound context predicate
      all_goals assumption
  | conjunctionIntroduction context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.conjunctionIntroduction_sound context first second
      all_goals assumption
  | conjunctionFirst context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.conjunctionFirst_sound context first second
      all_goals assumption
  | conjunctionSecond context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.conjunctionSecond_sound context first second
      all_goals assumption
  | disjunctionFirst context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.disjunctionFirst_sound context first second
      all_goals assumption
  | disjunctionSecond context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.disjunctionSecond_sound context first second
      all_goals assumption
  | disjunctionElimination context first second consequent =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      have premise4 := premises ⟨4, by simp [RuleCode.premises]⟩
      have premise5 := premises ⟨5, by simp [RuleCode.premises]⟩
      apply model.disjunctionElimination_sound stable context first second consequent
      all_goals assumption
  | implicationIntroduction context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.implicationIntroduction_sound stable context first second
      all_goals assumption
  | implicationElimination context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.implicationElimination_sound context first second
      all_goals assumption
  | universalIntroduction context domain predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.universalIntroduction_sound context domain predicate
      all_goals assumption
  | universalElimination context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.universalElimination_sound stable context domain predicate value
      all_goals assumption
  | existentialIntroduction context domain predicate value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.existentialIntroduction_sound stable context domain predicate value
      all_goals assumption
  | existentialElimination context domain predicate consequent =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      have premise4 := premises ⟨4, by simp [RuleCode.premises]⟩
      apply model.existentialElimination_sound stable context domain predicate consequent
      all_goals assumption
  | imageIntroduction context type value =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.imageIntroduction_sound context type value
      all_goals assumption
  | imageElimination context type predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.imageElimination_sound stable context type predicate
      all_goals assumption
  | substitutionWeakenAssumption context predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.substitutionWeakenAssumption_sound context predicate
      all_goals assumption
  | substitutionIntoAssumption source target predicate substitution =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.substitutionIntoAssumption_sound stable source target predicate substitution
      all_goals assumption
  | substitutionLift source target type substitution =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.substitutionLift_sound stable source target type substitution
      all_goals assumption
  | substitutionAssumptionLift source target predicate substitution =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.substitutionAssumptionLift_sound stable source target predicate substitution
      all_goals assumption
  | substitutePredicate source target substitution predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.substitutePredicate_sound stable source target substitution predicate
      all_goals assumption
  | substituteEntailment source target substitution predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.substituteEntailment_sound stable source target substitution predicate
      all_goals assumption
  | transportPredicate first second predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.transportPredicate_sound first second predicate
      all_goals assumption
  | transportEntailment first second predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.transportEntailment_sound first second predicate
      all_goals assumption
  | predicateReflexivity context predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.predicateReflexivity_sound context predicate
      all_goals assumption
  | predicateSymmetry context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.predicateSymmetry_sound context first second
      all_goals assumption
  | predicateTransitivity context first middle last =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.predicateTransitivity_sound context first middle last
      all_goals assumption
  | predicateExtensionality context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.predicateExtensionality_sound stable context first second
      all_goals assumption
  | entailmentConversion context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.entailmentConversion_sound context first second
      all_goals assumption
  | contextAssumeEquality first second firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.contextAssumeEquality_sound first second firstPredicate secondPredicate
      all_goals assumption
  | comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.comprehensionCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate
      all_goals assumption
  | quoteCongruence context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.quoteCongruence_sound context first second
      all_goals assumption
  | holdsCongruence context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.holdsCongruence_sound context first second
      all_goals assumption
  | imageCongruence context first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      apply model.imageCongruence_sound context first second
      all_goals assumption
  | refineCongruence context domain predicate first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      have premise4 := premises ⟨4, by simp [RuleCode.premises]⟩
      apply model.refineCongruence_sound stable context domain predicate first second
      all_goals assumption
  | forgetCongruence context domain predicate first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.forgetCongruence_sound context domain predicate first second
      all_goals assumption
  | predicatePrimitiveCongruence context symbol first second =>
      have earlier : D.predicateRank symbol < bound := ordered.2.1.1
      exact model.predicatePrimitiveCongruence_sound_before context symbol
        (realization.predicateHeader symbol earlier) first second
        (premises ⟨1, by simp [RuleCode.premises]⟩)
  | conjunctionCongruence context first second third fourth =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.conjunctionCongruence_sound context first second third fourth
      all_goals assumption
  | disjunctionCongruence context first second third fourth =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.disjunctionCongruence_sound context first second third fourth
      all_goals assumption
  | implicationCongruence context first second third fourth =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.implicationCongruence_sound context first second third fourth
      all_goals assumption
  | universalCongruence context firstDomain secondDomain firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.universalCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate
      all_goals assumption
  | existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      apply model.existentialCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate
      all_goals assumption
  | substitutePredicateEquality source target substitution first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.substitutePredicateEquality_sound stable source target substitution first second
      all_goals assumption
  | predicateSubstitutionCongruence source target first second predicate =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      apply model.predicateSubstitutionCongruence_sound stable source target first second predicate
      all_goals assumption
  | refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      have premise4 := premises ⟨4, by simp [RuleCode.premises]⟩
      have premise5 := premises ⟨5, by simp [RuleCode.premises]⟩
      have premise6 := premises ⟨6, by simp [RuleCode.premises]⟩
      apply model.refineAnnotationCongruence_sound stable context firstDomain secondDomain firstPredicate secondPredicate first second
      all_goals assumption
  | forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      have premise4 := premises ⟨4, by simp [RuleCode.premises]⟩
      apply model.forgetAnnotationCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate first second
      all_goals assumption
  | substitutionIntoAssumptionEquality source target predicate first second =>
      have premise0 := premises ⟨0, by simp [RuleCode.premises]⟩
      have premise1 := premises ⟨1, by simp [RuleCode.premises]⟩
      have premise2 := premises ⟨2, by simp [RuleCode.premises]⟩
      have premise3 := premises ⟨3, by simp [RuleCode.premises]⟩
      apply model.substitutionIntoAssumptionEquality_sound stable source target predicate first second
      all_goals assumption


end ModelData

namespace Derivation

theorem sound_before (model : ModelData S C localModel) {bound : Nat}
    (realization : BoundedRealization model D bound)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) {judgment : Judgment S}
    (derivation : Derivation D judgment) (ordered : derivation.before bound) :
    Interprets model judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment tree => Derivation.before (D := D) bound tree → Interprets model judgment)
    (fun rule premises ih => ?_) derivation ordered
  rcases rule with ⟨rule, rfl⟩
  intro bounded
  exact model.rule_sound_before realization stable beta eta rule bounded.1
    (fun position => ih ⟨position⟩ (bounded.2 ⟨position⟩))

theorem qualified_sound_before (model : ModelData S C localModel) {bound : Nat}
    (realization : BoundedRealization model D bound) (qualified : Qualification localModel)
    {judgment : Judgment S} (derivation : Derivation D judgment)
    (ordered : derivation.before bound) : Interprets model judgment :=
  sound_before model realization qualified.stableProducts qualified.productBeta
    qualified.productEta derivation ordered

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
