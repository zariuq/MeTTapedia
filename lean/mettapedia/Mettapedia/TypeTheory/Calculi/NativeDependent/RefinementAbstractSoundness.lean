import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractComputationSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractAssumptionSubstitutionSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessAssumptions

/-!
# Generated dependent judgments in arbitrary local predicate models

Every authored local rule constructs actual model families, sections,
predicates and guarded context maps from its local premises. The two binder
kinds retain their separate actions. Independent primitive meanings need
only their stated header and result realization. The whole theorem follows
by induction on the retained generated rule trees.

The model capabilities contain local logical operations and equations, not
whole-interpreter commutation or complete-judgment soundness fields. Product
stability, beta and eta are stated explicitly. Source classifying universality
and comparison of independently chosen model maps remain separate theorems.
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

/-- The declaration directly called by a primitive rule. Declarations that
occur in its arguments remain covered by their interpreted premises. -/
inductive PrimitiveDeclaration (S : Symbols.{a}) where
  | family : S.TypeSymbol → PrimitiveDeclaration S
  | term : S.TermSymbol → PrimitiveDeclaration S
  | predicate : S.PredicateSymbol → PrimitiveDeclaration S

inductive RuleDeclaration : RuleCode D → PrimitiveDeclaration S → Prop where
  | family {n : Nat} (context : ContextExpr S n) (symbol : S.TypeSymbol)
      (arguments : Substitution S (S.typeArity symbol) n) :
      RuleDeclaration (.typeFamily context symbol arguments) (.family symbol)
  | term {n : Nat} (context : ContextExpr S n) (symbol : S.TermSymbol)
      (arguments : Substitution S (S.termArity symbol) n) :
      RuleDeclaration (.primitive context symbol arguments) (.term symbol)
  | predicate {n : Nat} (context : ContextExpr S n) (symbol : S.PredicateSymbol)
      (arguments : Substitution S (S.predicateArity symbol) n) :
      RuleDeclaration (.predicatePrimitive context symbol arguments) (.predicate symbol)
  | familyCongruence {n : Nat} (context : ContextExpr S n) (symbol : S.TypeSymbol)
      (first second : Substitution S (S.typeArity symbol) n) :
      RuleDeclaration (.familyCongruence context symbol first second) (.family symbol)
  | primitiveCongruence {n : Nat} (context : ContextExpr S n) (symbol : S.TermSymbol)
      (first second : Substitution S (S.termArity symbol) n) :
      RuleDeclaration (.primitiveCongruence context symbol first second) (.term symbol)
  | predicateCongruence {n : Nat} (context : ContextExpr S n) (symbol : S.PredicateSymbol)
      (first second : Substitution S (S.predicateArity symbol) n) :
      RuleDeclaration (.predicatePrimitiveCongruence context symbol first second) (.predicate symbol)

namespace ModelData

/-- The readouts required by a single primitive declaration. -/
def realizesDeclaration (model : ModelData S C localModel) (D : Signature S) :
    PrimitiveDeclaration S → Prop
  | .family symbol =>
      model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol)
  | .term symbol =>
      model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol) ∧
      model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol)
  | .predicate symbol =>
      model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol)

section

variable (model : ModelData S C localModel) {n : Nat}

theorem family_sound_of_header (symbol : S.TypeSymbol)
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

theorem primitive_sound_of_header (symbol : S.TermSymbol)
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

theorem familyCongruence_sound_of_header (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (header : model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol))
    (first second : Substitution S (S.typeArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.typeParameters symbol) first second)) :
    Interprets model (.typeEq context (.family symbol first) (.family symbol second)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans header)
  exact ⟨Γ, model.familyAt symbol σ, contextRead,
    model.evaluate_family Γ symbol first σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead),
    model.evaluate_family Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem primitiveCongruence_sound_of_header (stable : StrictPiSubstitution localModel.products)
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

theorem predicatePrimitive_sound_of_header (symbol : S.PredicateSymbol)
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

theorem predicatePrimitiveCongruence_sound_of_header (context : ContextExpr S n) (symbol : S.PredicateSymbol)
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

end

theorem rule_sound_with_declaration (model : ModelData S C localModel)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) (rule : RuleCode D)
    (realized : ∀ declaration, RuleDeclaration rule declaration →
      model.realizesDeclaration D declaration)
    (premises : (position : Fin rule.premises.length) → Interprets model (rule.premises.get position)) :
    Interprets model rule.conclusion := by
  cases rule with
  | contextNil => exact model.contextNil_sound
  | contextExtend context type =>
      exact model.contextExtend_sound context type (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | «variable» context index => exact model.variable_sound stable context index (premises ⟨0, of_decide_eq_true rfl⟩)
  | typeFamily context symbol arguments =>
      have header := realized (.family symbol) (.family context symbol arguments)
      exact model.family_sound_of_header symbol header context arguments
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | primitive context symbol arguments =>
      have header := realized (.term symbol) (.term context symbol arguments)
      exact model.primitive_sound_of_header symbol header.1
        header.2 stable context arguments
        (premises ⟨3, of_decide_eq_true rfl⟩)
  | piFormation context domain body =>
      exact model.piFormation_sound context domain body (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | sigmaFormation context domain body =>
      exact model.sigmaFormation_sound context domain body (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | lambda context domain body term =>
      exact model.lambda_sound context domain body term
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | application context domain body function argument =>
      exact model.application_sound stable context domain body function argument
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | pairIntroduction context domain body first second =>
      exact model.pairIntroduction_sound stable context domain body first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | firstProjection context domain body pair =>
      exact model.firstProjection_sound context domain body pair
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | secondProjection context domain body pair =>
      exact model.secondProjection_sound stable context domain body pair
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | sigmaElimination context domain body motive branch pair =>
      exact model.sigmaElimination_sound stable context domain body motive branch pair
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
        (premises ⟨3, of_decide_eq_true rfl⟩) (premises ⟨4, of_decide_eq_true rfl⟩)
  | termConversion context term first second =>
      exact model.termConversion_sound context term first second (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | substitutionNil context => exact model.substitutionNil_sound context (premises ⟨0, of_decide_eq_true rfl⟩)
  | substitutionExtend source target type substitution term =>
      exact model.substitutionExtend_sound stable source target type substitution term
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | substitutionIdentity context => exact model.substitutionIdentity_sound context (premises ⟨0, of_decide_eq_true rfl⟩)
  | substitutionCompose source middle target first second =>
      exact model.substitutionCompose_sound stable source middle target first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | substitutionWeaken context type => exact model.substitutionWeaken_sound context type (premises ⟨0, of_decide_eq_true rfl⟩)
  | substituteType source target substitution type =>
      exact model.substituteType_sound stable source target substitution type
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | substituteTerm source target substitution term type =>
      exact model.substituteTerm_sound stable source target substitution term type
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | contextReflexivity context => exact model.contextReflexivity_sound context (premises ⟨0, of_decide_eq_true rfl⟩)
  | contextSymmetry first second => exact model.contextSymmetry_sound first second (premises ⟨0, of_decide_eq_true rfl⟩)
  | contextTransitivity first middle last =>
      exact model.contextTransitivity_sound first middle last (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | contextExtendEquality first second firstType secondType =>
      exact model.contextExtendEquality_sound first second firstType secondType
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | transportType first second type =>
      exact model.transportType_sound first second type (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | transportTerm first second term type =>
      exact model.transportTerm_sound first second term type (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | transportSubstitution source source' target target' substitution =>
      exact model.transportSubstitution_sound source source' target target' substitution
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | typeReflexivity context type => exact model.typeReflexivity_sound context type (premises ⟨0, of_decide_eq_true rfl⟩)
  | typeSymmetry context first second => exact model.typeSymmetry_sound context first second (premises ⟨0, of_decide_eq_true rfl⟩)
  | typeTransitivity context first middle last =>
      exact model.typeTransitivity_sound context first middle last (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | termReflexivity context term type => exact model.termReflexivity_sound context term type (premises ⟨0, of_decide_eq_true rfl⟩)
  | termSymmetry context first second type => exact model.termSymmetry_sound context first second type (premises ⟨0, of_decide_eq_true rfl⟩)
  | termTransitivity context first middle last type =>
      exact model.termTransitivity_sound context first middle last type (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | equalityConversion context first second firstType secondType =>
      exact model.equalityConversion_sound context first second firstType secondType
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | transportTypeEquality source target first second =>
      exact model.transportTypeEquality_sound source target first second (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | transportTermEquality source target first second type =>
      exact model.transportTermEquality_sound source target first second type (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | piCongruence context firstDomain secondDomain firstBody secondBody =>
      exact model.piCongruence_sound context firstDomain secondDomain firstBody secondBody
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | sigmaCongruence context firstDomain secondDomain firstBody secondBody =>
      exact model.sigmaCongruence_sound context firstDomain secondDomain firstBody secondBody
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | familyCongruence context symbol first second =>
      have header := realized (.family symbol) (.familyCongruence context symbol first second)
      exact model.familyCongruence_sound_of_header context symbol
        header first second
        (premises ⟨1, of_decide_eq_true rfl⟩)
  | primitiveCongruence context symbol first second =>
      have header := realized (.term symbol) (.primitiveCongruence context symbol first second)
      exact model.primitiveCongruence_sound_of_header stable context symbol
        header.1 header.2 first second
        (premises ⟨1, of_decide_eq_true rfl⟩)
  | lambdaCongruence context domain body first second =>
      exact model.lambdaAnnotationCongruence_sound context domain domain body body first second
        (model.typeReflexivity_sound context domain (premises ⟨0, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, of_decide_eq_true rfl⟩)) (premises ⟨2, of_decide_eq_true rfl⟩)
  | applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument =>
      exact model.applicationAnnotationCongruence_sound stable context domain domain body body
        firstFunction secondFunction firstArgument secondArgument
        (model.typeReflexivity_sound context domain (premises ⟨0, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, of_decide_eq_true rfl⟩))
        (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | pairCongruence context domain body firstLeft secondLeft firstRight secondRight =>
      exact model.pairAnnotationCongruence_sound stable context domain domain body body
        firstLeft secondLeft firstRight secondRight
        (model.typeReflexivity_sound context domain (premises ⟨0, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, of_decide_eq_true rfl⟩))
        (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | firstCongruence context domain body first second =>
      exact model.firstAnnotationCongruence_sound context domain domain body body first second
        (model.typeReflexivity_sound context domain (premises ⟨0, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, of_decide_eq_true rfl⟩)) (premises ⟨2, of_decide_eq_true rfl⟩)
  | secondCongruence context domain body first second =>
      exact model.secondAnnotationCongruence_sound stable context domain domain body body first second
        (model.typeReflexivity_sound context domain (premises ⟨0, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, of_decide_eq_true rfl⟩)) (premises ⟨2, of_decide_eq_true rfl⟩)
  | sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair =>
      exact model.sigmaEliminationAnnotationCongruence_sound stable context domain domain body body motive motive
        firstBranch secondBranch firstPair secondPair
        (model.typeReflexivity_sound context domain (premises ⟨0, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context domain) body (premises ⟨1, of_decide_eq_true rfl⟩))
        (model.typeReflexivity_sound (.snoc context (.sigma domain body)) motive (premises ⟨2, of_decide_eq_true rfl⟩))
        (premises ⟨3, of_decide_eq_true rfl⟩) (premises ⟨4, of_decide_eq_true rfl⟩)
  | lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
      exact model.lambdaAnnotationCongruence_sound context firstDomain secondDomain firstBody secondBody first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody
      firstFunction secondFunction firstArgument secondArgument =>
      exact model.applicationAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody
        firstFunction secondFunction firstArgument secondArgument
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩) (premises ⟨4, of_decide_eq_true rfl⟩)
  | pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight =>
      exact model.pairAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody
        firstLeft secondLeft firstRight secondRight
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩) (premises ⟨4, of_decide_eq_true rfl⟩)
  | firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
      exact model.firstAnnotationCongruence_sound context firstDomain secondDomain firstBody secondBody first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
      exact model.secondAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody
      firstMotive secondMotive firstBranch secondBranch firstPair secondPair =>
      exact model.sigmaEliminationAnnotationCongruence_sound stable context firstDomain secondDomain firstBody secondBody
        firstMotive secondMotive firstBranch secondBranch firstPair secondPair
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
        (premises ⟨5, of_decide_eq_true rfl⟩) (premises ⟨7, of_decide_eq_true rfl⟩)
  | piBeta context domain body term argument =>
      exact model.piBeta_sound stable beta context domain body term argument
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | piEta context domain body function =>
      exact model.piEta_sound stable eta context domain body function
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | sigmaFirstBeta context domain body first second =>
      exact model.sigmaFirstBeta_sound stable context domain body first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | sigmaSecondBeta context domain body first second =>
      exact model.sigmaSecondBeta_sound stable context domain body first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩) (premises ⟨3, of_decide_eq_true rfl⟩)
  | sigmaEta context domain body pair =>
      exact model.sigmaEta_sound context domain body pair
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | sigmaEliminationBeta context domain body motive branch first second =>
      exact model.sigmaEliminationBeta_sound stable context domain body motive branch first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
        (premises ⟨3, of_decide_eq_true rfl⟩) (premises ⟨4, of_decide_eq_true rfl⟩) (premises ⟨5, of_decide_eq_true rfl⟩)
  | sigmaEliminationEta context domain body motive term pair =>
      exact model.sigmaEliminationEta_sound stable context domain body motive term pair
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
        (premises ⟨3, of_decide_eq_true rfl⟩) (premises ⟨4, of_decide_eq_true rfl⟩)
  | substituteTypeEquality source target substitution first second =>
      exact model.substituteTypeEquality_sound stable source target substitution first second
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | substituteTermEquality source target substitution first second type =>
      exact model.substituteTermEquality_sound stable source target substitution first second type
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | substitutionReflexivity source target substitution =>
      exact model.substitutionReflexivity_sound source target substitution (premises ⟨0, of_decide_eq_true rfl⟩)
  | substitutionSymmetry source target first second =>
      exact model.substitutionSymmetry_sound source target first second (premises ⟨0, of_decide_eq_true rfl⟩)
  | substitutionTransitivity source target first middle last =>
      exact model.substitutionTransitivity_sound source target first middle last
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | substitutionExtendEquality source target type first second firstTerm secondTerm =>
      exact model.substitutionExtendEquality_sound stable source target type first second firstTerm secondTerm
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | typeSubstitutionCongruence source target first second type =>
      exact model.typeSubstitutionCongruence_sound stable source target first second type
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)
  | termSubstitutionCongruence source target first second term type =>
      exact model.termSubstitutionCongruence_sound stable source target first second term type
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨1, of_decide_eq_true rfl⟩)

  | contextAssume context predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.contextAssume_sound context predicate
      all_goals assumption
  | propositionType context =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.propositionType_sound context
      all_goals assumption
  | predicatePrimitive context symbol arguments =>
      have header := realized (.predicate symbol) (.predicate context symbol arguments)
      exact model.predicatePrimitive_sound_of_header symbol
        header context arguments
        (premises ⟨0, of_decide_eq_true rfl⟩) (premises ⟨2, of_decide_eq_true rfl⟩)
  | truthFormation context =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.truthFormation_sound context
      all_goals assumption
  | falsehoodFormation context =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.falsehoodFormation_sound context
      all_goals assumption
  | conjunctionFormation context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.conjunctionFormation_sound context first second
      all_goals assumption
  | disjunctionFormation context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.disjunctionFormation_sound context first second
      all_goals assumption
  | implicationFormation context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.implicationFormation_sound context first second
      all_goals assumption
  | universalFormation context domain predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.universalFormation_sound context domain predicate
      all_goals assumption
  | existentialFormation context domain predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.existentialFormation_sound context domain predicate
      all_goals assumption
  | holdsFormation context term =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.holdsFormation_sound context term
      all_goals assumption
  | imageFormation context type =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.imageFormation_sound context type
      all_goals assumption
  | quote context predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.quote_sound context predicate
      all_goals assumption
  | comprehensionFormation context domain predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.comprehensionFormation_sound context domain predicate
      all_goals assumption
  | comprehensionIntroduction context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.comprehensionIntroduction_sound stable context domain predicate value
      all_goals assumption
  | comprehensionElimination context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.comprehensionElimination_sound context domain predicate value
      all_goals assumption
  | comprehensionGuard context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.comprehensionGuard_sound stable context domain predicate value
      all_goals assumption
  | comprehensionBeta context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.comprehensionBeta_sound stable context domain predicate value
      all_goals assumption
  | comprehensionEta context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.comprehensionEta_sound context domain predicate value
      all_goals assumption
  | quoteHolds context term =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.quoteHolds_sound context term
      all_goals assumption
  | holdsQuote context predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.holdsQuote_sound context predicate
      all_goals assumption
  | hypothesis context predicate member =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.hypothesis_sound stable context predicate member
      all_goals assumption
  | truthIntroduction context =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.truthIntroduction_sound context
      all_goals assumption
  | falsehoodElimination context predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.falsehoodElimination_sound context predicate
      all_goals assumption
  | conjunctionIntroduction context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.conjunctionIntroduction_sound context first second
      all_goals assumption
  | conjunctionFirst context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.conjunctionFirst_sound context first second
      all_goals assumption
  | conjunctionSecond context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.conjunctionSecond_sound context first second
      all_goals assumption
  | disjunctionFirst context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.disjunctionFirst_sound context first second
      all_goals assumption
  | disjunctionSecond context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.disjunctionSecond_sound context first second
      all_goals assumption
  | disjunctionElimination context first second consequent =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      have premise4 := premises ⟨4, of_decide_eq_true rfl⟩
      have premise5 := premises ⟨5, of_decide_eq_true rfl⟩
      apply model.disjunctionElimination_sound stable context first second consequent
      all_goals assumption
  | implicationIntroduction context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.implicationIntroduction_sound stable context first second
      all_goals assumption
  | implicationElimination context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.implicationElimination_sound context first second
      all_goals assumption
  | universalIntroduction context domain predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.universalIntroduction_sound context domain predicate
      all_goals assumption
  | universalElimination context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.universalElimination_sound stable context domain predicate value
      all_goals assumption
  | existentialIntroduction context domain predicate value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.existentialIntroduction_sound stable context domain predicate value
      all_goals assumption
  | existentialElimination context domain predicate consequent =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      have premise4 := premises ⟨4, of_decide_eq_true rfl⟩
      apply model.existentialElimination_sound stable context domain predicate consequent
      all_goals assumption
  | imageIntroduction context type value =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.imageIntroduction_sound context type value
      all_goals assumption
  | imageElimination context type predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.imageElimination_sound stable context type predicate
      all_goals assumption
  | substitutionWeakenAssumption context predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.substitutionWeakenAssumption_sound context predicate
      all_goals assumption
  | substitutionIntoAssumption source target predicate substitution =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.substitutionIntoAssumption_sound stable source target predicate substitution
      all_goals assumption
  | substitutionLift source target type substitution =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.substitutionLift_sound stable source target type substitution
      all_goals assumption
  | substitutionAssumptionLift source target predicate substitution =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.substitutionAssumptionLift_sound stable source target predicate substitution
      all_goals assumption
  | substitutePredicate source target substitution predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.substitutePredicate_sound stable source target substitution predicate
      all_goals assumption
  | substituteEntailment source target substitution predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.substituteEntailment_sound stable source target substitution predicate
      all_goals assumption
  | transportPredicate first second predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.transportPredicate_sound first second predicate
      all_goals assumption
  | transportEntailment first second predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.transportEntailment_sound first second predicate
      all_goals assumption
  | predicateReflexivity context predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.predicateReflexivity_sound context predicate
      all_goals assumption
  | predicateSymmetry context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.predicateSymmetry_sound context first second
      all_goals assumption
  | predicateTransitivity context first middle last =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.predicateTransitivity_sound context first middle last
      all_goals assumption
  | predicateExtensionality context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.predicateExtensionality_sound stable context first second
      all_goals assumption
  | entailmentConversion context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.entailmentConversion_sound context first second
      all_goals assumption
  | contextAssumeEquality first second firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.contextAssumeEquality_sound first second firstPredicate secondPredicate
      all_goals assumption
  | comprehensionCongruence context firstDomain secondDomain firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.comprehensionCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate
      all_goals assumption
  | quoteCongruence context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.quoteCongruence_sound context first second
      all_goals assumption
  | holdsCongruence context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.holdsCongruence_sound context first second
      all_goals assumption
  | imageCongruence context first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      apply model.imageCongruence_sound context first second
      all_goals assumption
  | refineCongruence context domain predicate first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      have premise4 := premises ⟨4, of_decide_eq_true rfl⟩
      apply model.refineCongruence_sound stable context domain predicate first second
      all_goals assumption
  | forgetCongruence context domain predicate first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.forgetCongruence_sound context domain predicate first second
      all_goals assumption
  | predicatePrimitiveCongruence context symbol first second =>
      have header := realized (.predicate symbol) (.predicateCongruence context symbol first second)
      exact model.predicatePrimitiveCongruence_sound_of_header context symbol
        header first second
        (premises ⟨1, of_decide_eq_true rfl⟩)
  | conjunctionCongruence context first second third fourth =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.conjunctionCongruence_sound context first second third fourth
      all_goals assumption
  | disjunctionCongruence context first second third fourth =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.disjunctionCongruence_sound context first second third fourth
      all_goals assumption
  | implicationCongruence context first second third fourth =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.implicationCongruence_sound context first second third fourth
      all_goals assumption
  | universalCongruence context firstDomain secondDomain firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.universalCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate
      all_goals assumption
  | existentialCongruence context firstDomain secondDomain firstPredicate secondPredicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      apply model.existentialCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate
      all_goals assumption
  | substitutePredicateEquality source target substitution first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.substitutePredicateEquality_sound stable source target substitution first second
      all_goals assumption
  | predicateSubstitutionCongruence source target first second predicate =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      apply model.predicateSubstitutionCongruence_sound stable source target first second predicate
      all_goals assumption
  | refineAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      have premise4 := premises ⟨4, of_decide_eq_true rfl⟩
      have premise5 := premises ⟨5, of_decide_eq_true rfl⟩
      have premise6 := premises ⟨6, of_decide_eq_true rfl⟩
      apply model.refineAnnotationCongruence_sound stable context firstDomain secondDomain firstPredicate secondPredicate first second
      all_goals assumption
  | forgetAnnotationCongruence context firstDomain secondDomain firstPredicate secondPredicate first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      have premise4 := premises ⟨4, of_decide_eq_true rfl⟩
      apply model.forgetAnnotationCongruence_sound context firstDomain secondDomain firstPredicate secondPredicate first second
      all_goals assumption
  | substitutionIntoAssumptionEquality source target predicate first second =>
      have premise0 := premises ⟨0, of_decide_eq_true rfl⟩
      have premise1 := premises ⟨1, of_decide_eq_true rfl⟩
      have premise2 := premises ⟨2, of_decide_eq_true rfl⟩
      have premise3 := premises ⟨3, of_decide_eq_true rfl⟩
      apply model.substitutionIntoAssumptionEquality_sound stable source target predicate first second
      all_goals assumption

theorem rule_sound (model : ModelData S C localModel) (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) (rule : RuleCode D)
    (premises : (position : Fin rule.premises.length) → Interprets model (rule.premises.get position)) :
    Interprets model rule.conclusion := by
  apply model.rule_sound_with_declaration stable beta eta rule ?_ premises
  intro declaration _
  cases declaration with
  | family symbol => exact realization.typeHeader symbol
  | term symbol => exact ⟨realization.termHeader symbol, realization.termResult symbol⟩
  | predicate symbol => exact realization.predicateHeader symbol

end ModelData

namespace Derivation

theorem sound (model : ModelData S C localModel) (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) {judgment : Judgment S}
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

/-- Local product qualifications discharge the three explicit product
premises without adding any whole-judgment premise. -/
theorem qualified_sound (model : ModelData S C localModel)
    (realization : SignatureRealization model D) (qualified : Qualification localModel)
    {judgment : Judgment S} (derivation : Derivation D judgment) : Interprets model judgment :=
  sound model realization qualified.stableProducts qualified.productBeta qualified.productEta derivation

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
