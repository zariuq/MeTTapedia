import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalJudgmentRegularitySubstitution

/-!
# Regularity of all generated external dependent judgments

The simultaneous derivation induction earns formation of contexts and result
families, and actual typed admissions of both sides of every generated equation.
Changing Church annotations and dependent result types uses the local equality,
substitution and conversion rules. No semantic soundness premise is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External
namespace JudgmentRegularity

open Contextual

universe u
variable {S : Symbols.{u}} {D : Signature S}

structure TermInfo {n : Nat} (D : Signature S) (context : ContextExpr S n) (type : TypeExpr S n) : Prop where
  contextFormed : Formed D context
  typeFormed : Holds D (.type context type)

structure SubstitutionInfo {n m : Nat} (D : Signature S)
    (source : ContextExpr S n) (target : ContextExpr S m) : Prop where
  sourceFormed : Formed D source
  targetFormed : Formed D target

structure ContextEquationInfo {n : Nat} (D : Signature S)
    (first second : ContextExpr S n) : Prop where
  firstFormed : Formed D first
  secondFormed : Formed D second

structure TypeEquationInfo {n : Nat} (D : Signature S) (context : ContextExpr S n)
    (first second : TypeExpr S n) : Prop where
  contextFormed : Formed D context
  firstTyped : Holds D (.type context first)
  secondTyped : Holds D (.type context second)

structure TermEquationInfo {n : Nat} (D : Signature S) (context : ContextExpr S n)
    (first second : TermExpr S n) (type : TypeExpr S n) : Prop where
  contextFormed : Formed D context
  typeFormed : Holds D (.type context type)
  firstTyped : Holds D (.term context first type)
  secondTyped : Holds D (.term context second type)

structure SubstitutionEquationInfo {n m : Nat} (D : Signature S)
    (source : ContextExpr S n) (target : ContextExpr S m)
    (first second : Substitution S m n) : Prop where
  sourceFormed : Formed D source
  targetFormed : Formed D target
  firstTyped : Holds D (.substitution source target first)
  secondTyped : Holds D (.substitution source target second)

def Result (D : Signature S) : Judgment S → Prop
  | .context context => Formed D context
  | .type context _ => Formed D context
  | .term context _ type => TermInfo D context type
  | .substitution source target _ => SubstitutionInfo D source target
  | .contextEq first second => ContextEquationInfo D first second
  | .typeEq context first second => TypeEquationInfo D context first second
  | .termEq context first second type => TermEquationInfo D context first second type
  | .substitutionEq source target first second => SubstitutionEquationInfo D source target first second

theorem ruleRegularity (code : RuleCode D)
    (premises : ∀ position : Fin code.premises.length, Holds D (code.premises.get position))
    (regular : ∀ position : Fin code.premises.length, Result D (code.premises.get position)) :
    Result D code.conclusion := by
  cases code with
  | contextNil =>
    exact .nil
  | contextExtend context type =>
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact .snoc r0 p1
  | «variable» context index =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, r0.lookup index⟩
  | typeFamily context symbol arguments =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact r0
  | primitive context symbol arguments =>
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, typeSubstitute p3 p2⟩
  | piFormation context domain body =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact r0
  | sigmaFormation context domain body =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact r0
  | lambda context domain body term =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, conclude (.piFormation context domain body) ⟨p0, p1, trivial⟩⟩
  | application context domain body function argument =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, typeAt r0 p0 p1 p3⟩
  | pairIntroduction context domain body first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩⟩
  | firstProjection context domain body pair =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, p0⟩
  | secondProjection context domain body pair =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have first := conclude (.firstProjection context domain body pair) ⟨p0, p1, p2, trivial⟩
    exact ⟨r0, typeAt r0 p0 p1 first⟩
  | sigmaElimination context domain body motive branch pair =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have sigma := conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩
    exact ⟨r0, typeAt r0 sigma p2 p4⟩
  | termConversion context term first second =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r1.secondTyped⟩
  | substitutionNil context =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, .nil⟩
  | substitutionExtend source target type substitution term =>
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, .snoc r0.targetFormed p1⟩
  | substitutionIdentity context =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, r0⟩
  | substitutionCompose source middle target first second =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, r1.targetFormed⟩
  | substitutionWeaken context type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨.snoc r0 p0, r0⟩
  | substituteType source target substitution type =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact r0.sourceFormed
  | substituteTerm source target substitution term type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, typeSubstitute p0 r1.typeFormed⟩
  | contextReflexivity context =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, r0⟩
  | contextSymmetry first second =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.secondFormed, r0.firstFormed⟩
  | contextTransitivity first middle last =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.firstFormed, r1.secondFormed⟩
  | contextExtendEquality first second firstType secondType =>
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨.snoc r0.firstFormed r1.firstTyped, .snoc r0.secondFormed p2⟩
  | transportType first second type =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact r0.secondFormed
  | transportTerm first second term type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have formed := conclude (.transportType first second type) ⟨p0, r1.typeFormed, trivial⟩
    exact ⟨r0.secondFormed, formed⟩
  | transportSubstitution source sourceNew target targetNew substitution =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.secondFormed, r1.secondFormed⟩
  | typeReflexivity context type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0, p0, p0⟩
  | typeSymmetry context first second =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r0.secondTyped, r0.firstTyped⟩
  | typeTransitivity context first middle last =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r0.firstTyped, r1.secondTyped⟩
  | termReflexivity context term type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r0.typeFormed, p0, p0⟩
  | termSymmetry context first second type =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r0.typeFormed, r0.secondTyped, r0.firstTyped⟩
  | termTransitivity context first middle last type =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r0.typeFormed, r0.firstTyped, r1.secondTyped⟩
  | equalityConversion context first second firstType secondType =>
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.contextFormed, r1.secondTyped, convert r0.firstTyped p1, convert r0.secondTyped p1⟩
  | transportTypeEquality source target first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.transportType source target first) ⟨p0, r1.firstTyped, trivial⟩
    have secondTyped := conclude (.transportType source target second) ⟨p0, r1.secondTyped, trivial⟩
    exact ⟨r0.secondFormed, firstTyped, secondTyped⟩
  | transportTermEquality source target first second type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have typeTyped := conclude (.transportType source target type) ⟨p0, r1.typeFormed, trivial⟩
    have firstTyped := conclude (.transportTerm source target first type) ⟨p0, r1.firstTyped, trivial⟩
    have secondTyped := conclude (.transportTerm source target second type) ⟨p0, r1.secondTyped, trivial⟩
    exact ⟨r0.secondFormed, typeTyped, firstTyped, secondTyped⟩
  | piCongruence context firstDomain secondDomain firstBody secondBody =>
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have first := conclude (.piFormation context firstDomain firstBody) ⟨r0.firstTyped, r1.firstTyped, trivial⟩
    have second := conclude (.piFormation context secondDomain secondBody) ⟨r0.secondTyped, p2, trivial⟩
    exact ⟨r0.contextFormed, first, second⟩
  | sigmaCongruence context firstDomain secondDomain firstBody secondBody =>
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have first := conclude (.sigmaFormation context firstDomain firstBody) ⟨r0.firstTyped, r1.firstTyped, trivial⟩
    have second := conclude (.sigmaFormation context secondDomain secondBody) ⟨r0.secondTyped, p2, trivial⟩
    exact ⟨r0.contextFormed, first, second⟩
  | familyCongruence context symbol first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.typeFamily context symbol first) ⟨r1.sourceFormed.judgment, p0, r1.firstTyped, trivial⟩
    have secondTyped := conclude (.typeFamily context symbol second) ⟨r1.sourceFormed.judgment, p0, r1.secondTyped, trivial⟩
    exact ⟨r1.sourceFormed, firstTyped, secondTyped⟩
  | primitiveCongruence context symbol first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.primitive context symbol first)
      ⟨r1.sourceFormed.judgment, r0.judgment, p0, r1.firstTyped, trivial⟩
    have secondTyped := conclude (.primitive context symbol second)
      ⟨r1.sourceFormed.judgment, r0.judgment, p0, r1.secondTyped, trivial⟩
    have types := conclude (.typeSubstitutionCongruence context (D.termParameters symbol) first second (D.termResult symbol))
      ⟨p1, p0, trivial⟩
    exact ⟨r1.sourceFormed, typeSubstitute r1.firstTyped p0, firstTyped, convert secondTyped (typeSymmetry types)⟩
  | lambdaCongruence context domain body first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r2 := regular ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.lambda context domain body first) ⟨p0, p1, r2.firstTyped, trivial⟩
    have secondTyped := conclude (.lambda context domain body second) ⟨p0, p1, r2.secondTyped, trivial⟩
    exact ⟨r0, conclude (.piFormation context domain body) ⟨p0, p1, trivial⟩, firstTyped, secondTyped⟩
  | applicationCongruence context domain body firstFunction secondFunction firstArgument secondArgument =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r2 := regular ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.application context domain body firstFunction firstArgument)
      ⟨p0, p1, r2.firstTyped, r3.firstTyped, trivial⟩
    have secondTyped := conclude (.application context domain body secondFunction secondArgument)
      ⟨p0, p1, r2.secondTyped, r3.secondTyped, trivial⟩
    have types := typeAtArgumentEquality r0 p0 p1 p3 r3.secondTyped
    exact ⟨r0, typeAt r0 p0 p1 r3.firstTyped, firstTyped, convert secondTyped (typeSymmetry types)⟩
  | pairCongruence context domain body firstLeft secondLeft firstRight secondRight =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r2 := regular ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.pairIntroduction context domain body firstLeft firstRight)
      ⟨p0, p1, r2.firstTyped, r3.firstTyped, trivial⟩
    have secondTyped := conclude (.pairIntroduction context domain body secondLeft secondRight)
      ⟨p0, p1, r2.secondTyped, p4, trivial⟩
    exact ⟨r0, conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩, firstTyped, secondTyped⟩
  | firstCongruence context domain body first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r2 := regular ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.firstProjection context domain body first) ⟨p0, p1, r2.firstTyped, trivial⟩
    have secondTyped := conclude (.firstProjection context domain body second) ⟨p0, p1, r2.secondTyped, trivial⟩
    exact ⟨r0, p0, firstTyped, secondTyped⟩
  | secondCongruence context domain body first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r2 := regular ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstProjection := conclude (.firstProjection context domain body first) ⟨p0, p1, r2.firstTyped, trivial⟩
    have secondProjection := conclude (.firstProjection context domain body second) ⟨p0, p1, r2.secondTyped, trivial⟩
    have projections := conclude (.firstCongruence context domain body first second) ⟨p0, p1, p2, trivial⟩
    have types := typeAtArgumentEquality r0 p0 p1 projections secondProjection
    have firstTyped := conclude (.secondProjection context domain body first) ⟨p0, p1, r2.firstTyped, trivial⟩
    have secondTyped := conclude (.secondProjection context domain body second) ⟨p0, p1, r2.secondTyped, trivial⟩
    exact ⟨r0, typeAt r0 p0 p1 firstProjection, firstTyped, convert secondTyped (typeSymmetry types)⟩
  | sigmaEliminationCongruence context domain body motive firstBranch secondBranch firstPair secondPair =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r4 := regular ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have sigma := conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩
    have firstTyped := conclude (.sigmaElimination context domain body motive firstBranch firstPair)
      ⟨p0, p1, p2, r3.firstTyped, r4.firstTyped, trivial⟩
    have secondTyped := conclude (.sigmaElimination context domain body motive secondBranch secondPair)
      ⟨p0, p1, p2, r3.secondTyped, r4.secondTyped, trivial⟩
    have types := typeAtArgumentEquality r0 sigma p2 p4 r4.secondTyped
    exact ⟨r0, typeAt r0 sigma p2 r4.firstTyped, firstTyped, convert secondTyped (typeSymmetry types)⟩
  | lambdaAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.lambda context firstDomain firstBody first)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, trivial⟩
    have secondTyped := conclude (.lambda context secondDomain secondBody second)
      ⟨r0.secondTyped, p2, p4, trivial⟩
    have types := conclude (.piCongruence context firstDomain secondDomain firstBody secondBody) ⟨p0, p1, p2, trivial⟩
    have formed := conclude (.piFormation context firstDomain firstBody) ⟨r0.firstTyped, r1.firstTyped, trivial⟩
    exact ⟨r0.contextFormed, formed, firstTyped, convert secondTyped (typeSymmetry types)⟩
  | applicationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstFunction secondFunction firstArgument secondArgument =>
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p5 := premises ⟨5, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p6 := premises ⟨6, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r4 := regular ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.application context firstDomain firstBody firstFunction firstArgument)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, r4.firstTyped, trivial⟩
    have secondTyped := conclude (.application context secondDomain secondBody secondFunction secondArgument)
      ⟨r0.secondTyped, p2, p5, p6, trivial⟩
    have types := typeAtCongruence r0.contextFormed r0.firstTyped r1.firstTyped p1 p4 r4.secondTyped
    exact ⟨r0.contextFormed, typeAt r0.contextFormed r0.firstTyped r1.firstTyped r4.firstTyped,
      firstTyped, convert secondTyped (typeSymmetry types)⟩
  | pairAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p5 := premises ⟨5, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p6 := premises ⟨6, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r4 := regular ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.pairIntroduction context firstDomain firstBody firstLeft firstRight)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, r4.firstTyped, trivial⟩
    have secondTyped := conclude (.pairIntroduction context secondDomain secondBody secondLeft secondRight)
      ⟨r0.secondTyped, p2, p5, p6, trivial⟩
    have types := conclude (.sigmaCongruence context firstDomain secondDomain firstBody secondBody) ⟨p0, p1, p2, trivial⟩
    have formed := conclude (.sigmaFormation context firstDomain firstBody) ⟨r0.firstTyped, r1.firstTyped, trivial⟩
    exact ⟨r0.contextFormed, formed, firstTyped, convert secondTyped (typeSymmetry types)⟩
  | firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.firstProjection context firstDomain firstBody first)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, trivial⟩
    have secondTyped := conclude (.firstProjection context secondDomain secondBody second)
      ⟨r0.secondTyped, p2, p4, trivial⟩
    exact ⟨r0.contextFormed, r0.firstTyped, firstTyped, convert secondTyped (typeSymmetry p0)⟩
  | secondAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstProjection := conclude (.firstProjection context firstDomain firstBody first)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, trivial⟩
    have secondProjection := conclude (.firstProjection context secondDomain secondBody second)
      ⟨r0.secondTyped, p2, p4, trivial⟩
    have projections := conclude (.firstAnnotationCongruence context firstDomain secondDomain firstBody secondBody first second)
      ⟨p0, p1, p2, p3, p4, trivial⟩
    have secondAtFirst := convert secondProjection (typeSymmetry p0)
    have types := typeAtCongruence r0.contextFormed r0.firstTyped r1.firstTyped p1 projections secondAtFirst
    have firstTyped := conclude (.secondProjection context firstDomain firstBody first)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, trivial⟩
    have secondTyped := conclude (.secondProjection context secondDomain secondBody second)
      ⟨r0.secondTyped, p2, p4, trivial⟩
    exact ⟨r0.contextFormed, typeAt r0.contextFormed r0.firstTyped r1.firstTyped firstProjection,
      firstTyped, convert secondTyped (typeSymmetry types)⟩
  | sigmaEliminationAnnotationCongruence context firstDomain secondDomain firstBody secondBody firstMotive secondMotive firstBranch secondBranch firstPair secondPair =>
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p6 := premises ⟨6, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p7 := premises ⟨7, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p8 := premises ⟨8, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r3 := regular ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r5 := regular ⟨5, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r7 := regular ⟨7, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have sigma := conclude (.sigmaFormation context firstDomain firstBody) ⟨r0.firstTyped, r1.firstTyped, trivial⟩
    have firstTyped := conclude (.sigmaElimination context firstDomain firstBody firstMotive firstBranch firstPair)
      ⟨r0.firstTyped, r1.firstTyped, r3.firstTyped, r5.firstTyped, r7.firstTyped, trivial⟩
    have secondTyped := conclude (.sigmaElimination context secondDomain secondBody secondMotive secondBranch secondPair)
      ⟨r0.secondTyped, p2, p4, p6, p8, trivial⟩
    have types := typeAtCongruence r0.contextFormed sigma r3.firstTyped p3 p7 r7.secondTyped
    exact ⟨r0.contextFormed, typeAt r0.contextFormed sigma r3.firstTyped r7.firstTyped,
      firstTyped, convert secondTyped (typeSymmetry types)⟩
  | piBeta context domain body term argument =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have function := conclude (.lambda context domain body term) ⟨p0, p1, p2, trivial⟩
    have firstTyped := conclude (.application context domain body (.lam domain body term) argument)
      ⟨p0, p1, function, p3, trivial⟩
    exact ⟨r0, typeAt r0 p0 p1 p3, firstTyped, termAt r0 p0 p2 p3⟩
  | piEta context domain body function =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have formed := conclude (.piFormation context domain body) ⟨p0, p1, trivial⟩
    exact ⟨r0, formed, piEtaAdmission r0 p0 p1 p2, p2⟩
  | sigmaFirstBeta context domain body first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have pair := conclude (.pairIntroduction context domain body first second) ⟨p0, p1, p2, p3, trivial⟩
    have firstTyped := conclude (.firstProjection context domain body (.pair domain body first second)) ⟨p0, p1, pair, trivial⟩
    exact ⟨r0, p0, firstTyped, p2⟩
  | sigmaSecondBeta context domain body first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have pair := conclude (.pairIntroduction context domain body first second) ⟨p0, p1, p2, p3, trivial⟩
    have firstTyped := conclude (.secondProjection context domain body (.pair domain body first second)) ⟨p0, p1, pair, trivial⟩
    have firsts := conclude (.sigmaFirstBeta context domain body first second) ⟨p0, p1, p2, p3, trivial⟩
    have types := typeAtArgumentEquality r0 p0 p1 firsts p2
    exact ⟨r0, typeAt r0 p0 p1 p2, convert firstTyped types, p3⟩
  | sigmaEta context domain body pair =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have first := conclude (.firstProjection context domain body pair) ⟨p0, p1, p2, trivial⟩
    have second := conclude (.secondProjection context domain body pair) ⟨p0, p1, p2, trivial⟩
    have firstTyped := conclude (.pairIntroduction context domain body (.fst domain body pair) (.snd domain body pair))
      ⟨p0, p1, first, second, trivial⟩
    exact ⟨r0, conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩, firstTyped, p2⟩
  | sigmaEliminationBeta context domain body motive branch first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p5 := premises ⟨5, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have sigma := conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩
    have paired := conclude (.pairIntroduction context domain body first second) ⟨p0, p1, p4, p5, trivial⟩
    have firstTyped := conclude (.sigmaElimination context domain body motive branch (.pair domain body first second))
      ⟨p0, p1, p2, p3, paired, trivial⟩
    have secondSubstituted := termSubstitute (components r0 p0 p1 p4 p5) p3
    have secondTyped : Holds D (.term context (branch.substitute (instantiateComponents first second))
        (motive.substitute (instantiate (.pair domain body first second)))) := by
      simpa only [TypeExpr.pairMotive_instantiate] using secondSubstituted
    exact ⟨r0, typeAt r0 sigma p2 paired, firstTyped, secondTyped⟩
  | sigmaEliminationEta context domain body motive term pair =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p2 := premises ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p4 := premises ⟨4, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have sigma := conclude (.sigmaFormation context domain body) ⟨p0, p1, trivial⟩
    have branch := termSubstitute (pack r0 p0 p1) p3
    have firstTyped := conclude (.sigmaElimination context domain body motive (term.substitute (packSubstitution domain body)) pair)
      ⟨p0, p1, p2, branch, p4, trivial⟩
    exact ⟨r0, typeAt r0 sigma p2 p4, firstTyped, termAt r0 sigma p3 p4⟩
  | substituteTypeEquality source target substitution first second =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, typeSubstitute p0 r1.firstTyped, typeSubstitute p0 r1.secondTyped⟩
  | substituteTermEquality source target substitution first second type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, typeSubstitute p0 r1.typeFormed,
      termSubstitute p0 r1.firstTyped, termSubstitute p0 r1.secondTyped⟩
  | substitutionReflexivity source target substitution =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, r0.targetFormed, p0, p0⟩
  | substitutionSymmetry source target first second =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, r0.targetFormed, r0.secondTyped, r0.firstTyped⟩
  | substitutionTransitivity source target first middle last =>
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, r0.targetFormed, r0.firstTyped, r1.secondTyped⟩
  | substitutionExtendEquality source target type first second firstTerm secondTerm =>
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p3 := premises ⟨3, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r2 := regular ⟨2, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have firstTyped := conclude (.substitutionExtend source target type first firstTerm) ⟨r0.firstTyped, p1, r2.firstTyped, trivial⟩
    have secondTyped := conclude (.substitutionExtend source target type second secondTerm) ⟨r0.secondTyped, p1, p3, trivial⟩
    exact ⟨r0.sourceFormed, .snoc r0.targetFormed p1, firstTyped, secondTyped⟩
  | typeSubstitutionCongruence source target first second type =>
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    exact ⟨r0.sourceFormed, typeSubstitute r0.firstTyped p1, typeSubstitute r0.secondTyped p1⟩
  | termSubstitutionCongruence source target first second term type =>
    have p0 := premises ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have p1 := premises ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r0 := regular ⟨0, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have r1 := regular ⟨1, by simp only [RuleCode.premises, List.length_cons, List.length_nil]; omega⟩
    have types := conclude (.typeSubstitutionCongruence source target first second type) ⟨p0, r1.typeFormed, trivial⟩
    exact ⟨r0.sourceFormed, typeSubstitute r0.firstTyped r1.typeFormed,
      termSubstitute r0.firstTyped p1, convert (termSubstitute r0.secondTyped p1) (typeSymmetry types)⟩

/-- Regularity is computed from the supplied actual generated derivation. -/
theorem derivation {judgment : Judgment S} (tree : Derivation D judgment) : Result D judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment _ => Result D judgment) (fun rule premises regular => ?_) tree
  rcases rule with ⟨code, rfl⟩
  exact ruleRegularity code (fun position => ⟨premises ⟨position⟩⟩) (fun position => regular ⟨position⟩)

theorem holds {judgment : Judgment S} (admitted : Holds D judgment) : Result D judgment := by
  rcases admitted with ⟨tree⟩
  exact derivation tree

theorem typeContext {n : Nat} {context : ContextExpr S n} {type : TypeExpr S n}
    (typed : Holds D (.type context type)) : Formed D context := holds typed

theorem termContext {n : Nat} {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (typed : Holds D (.term context term type)) : Formed D context := (holds typed).contextFormed

theorem termType {n : Nat} {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (typed : Holds D (.term context term type)) : Holds D (.type context type) := (holds typed).typeFormed

theorem substitutionContexts {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} (admitted : Holds D (.substitution source target substitution)) :
    Formed D source ∧ Formed D target := ⟨(holds admitted).sourceFormed, (holds admitted).targetFormed⟩

theorem contextEquality {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second)) : Formed D first ∧ Formed D second :=
  ⟨(holds same).firstFormed, (holds same).secondFormed⟩

theorem typeEquality {n : Nat} {context : ContextExpr S n} {first second : TypeExpr S n}
    (same : Holds D (.typeEq context first second)) :
    Holds D (.type context first) ∧ Holds D (.type context second) :=
  ⟨(holds same).firstTyped, (holds same).secondTyped⟩

theorem termEquality {n : Nat} {context : ContextExpr S n} {first second : TermExpr S n}
    {type : TypeExpr S n} (same : Holds D (.termEq context first second type)) :
    Holds D (.term context first type) ∧ Holds D (.term context second type) :=
  ⟨(holds same).firstTyped, (holds same).secondTyped⟩

theorem substitutionEquality {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {first second : Substitution S m n} (same : Holds D (.substitutionEq source target first second)) :
    Holds D (.substitution source target first) ∧ Holds D (.substitution source target second) :=
  ⟨(holds same).firstTyped, (holds same).secondTyped⟩

end JudgmentRegularity
end Mettapedia.TypeTheory.Calculi.NativeDependent.External
