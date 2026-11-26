import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementStructuralSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPairContextInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractCongruenceSoundness

/-!
# Annotation-sensitive constructor equations in dependent models

Converted domain, codomain and full-motive annotations are interpreted by
the same actual model data. The constructor equations follow from evaluating
their supplied term equations at those shared dependent types. Primitive
argument equations retain their actual dependent telescope arrows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {D : Signature S}

namespace ModelData

attribute [local irreducible] products sums TypeOver.extensionSubstitution
  ContextualSumComprehension.normalize ContextualSumComprehension.reindexBody

variable (model : ModelData S C) {n : Nat}

theorem piCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody)) :
    Interprets model (.typeEq context (.pi firstDomain firstBody) (.pi secondDomain secondBody)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.piCongruence_sound model.toAbstract context firstDomain secondDomain firstBody
      secondBody domainsInterpreted.toAbstract bodiesInterpreted.toAbstract)

theorem sigmaCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody)) :
    Interprets model (.typeEq context (.sigma firstDomain firstBody) (.sigma secondDomain secondBody)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaCongruence_sound model.toAbstract context firstDomain secondDomain firstBody
      secondBody domainsInterpreted.toAbstract bodiesInterpreted.toAbstract)

theorem familyCongruence_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (first second : Substitution S (S.typeArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.typeParameters symbol) first second)) :
    Interprets model (.typeEq context (.family symbol first) (.family symbol second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.familyCongruence_sound model.toAbstract realization.toAbstract context symbol
      first second argumentsInterpreted.toAbstract)

theorem primitiveCongruence_sound (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (first second : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.termParameters symbol) first second)) :
    Interprets model (.termEq context (.primitive symbol first) (.primitive symbol second)
      ((D.termResult symbol).substitute first)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.primitiveCongruence_sound model.toAbstract realization.toAbstract
      (model.stable_toAbstract stable) context symbol first second argumentsInterpreted.toAbstract)

theorem lambdaAnnotationCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (first second : TermExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (termsInterpreted : Interprets model (.termEq (.snoc context firstDomain) first second firstBody)) :
    Interprets model (.termEq context (.lam firstDomain firstBody first) (.lam secondDomain secondBody second)
      (.pi firstDomain firstBody)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.lambdaAnnotationCongruence_sound model.toAbstract context firstDomain secondDomain
      firstBody secondBody first second domainsInterpreted.toAbstract bodiesInterpreted.toAbstract
      termsInterpreted.toAbstract)

theorem applicationAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstBody secondBody : TypeExpr S (n + 1))
    (firstFunction secondFunction firstArgument secondArgument : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (functionsInterpreted : Interprets model (.termEq context firstFunction secondFunction (.pi firstDomain firstBody)))
    (argumentsInterpreted : Interprets model (.termEq context firstArgument secondArgument firstDomain)) :
    Interprets model (.termEq context (.app firstDomain firstBody firstFunction firstArgument)
      (.app secondDomain secondBody secondFunction secondArgument)
        (firstBody.substitute (instantiate firstArgument))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.applicationAnnotationCongruence_sound model.toAbstract
      (model.stable_toAbstract stable) context firstDomain secondDomain firstBody secondBody firstFunction
      secondFunction firstArgument secondArgument domainsInterpreted.toAbstract
      bodiesInterpreted.toAbstract functionsInterpreted.toAbstract argumentsInterpreted.toAbstract)

theorem pairAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstBody secondBody : TypeExpr S (n + 1)) (firstLeft secondLeft firstRight secondRight : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (firstInterpreted : Interprets model (.termEq context firstLeft secondLeft firstDomain))
    (secondInterpreted : Interprets model (.termEq context firstRight secondRight (firstBody.substitute (instantiate firstLeft)))) :
    Interprets model (.termEq context (.pair firstDomain firstBody firstLeft firstRight)
      (.pair secondDomain secondBody secondLeft secondRight) (.sigma firstDomain firstBody)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.pairAnnotationCongruence_sound model.toAbstract (model.stable_toAbstract stable)
      context firstDomain secondDomain firstBody secondBody firstLeft secondLeft firstRight secondRight
      domainsInterpreted.toAbstract bodiesInterpreted.toAbstract firstInterpreted.toAbstract
      secondInterpreted.toAbstract)

theorem firstAnnotationCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (pairsInterpreted : Interprets model (.termEq context first second (.sigma firstDomain firstBody))) :
    Interprets model (.termEq context (.fst firstDomain firstBody first) (.fst secondDomain secondBody second) firstDomain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.firstAnnotationCongruence_sound model.toAbstract context firstDomain secondDomain
      firstBody secondBody first second domainsInterpreted.toAbstract bodiesInterpreted.toAbstract
      pairsInterpreted.toAbstract)

theorem secondAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstBody secondBody : TypeExpr S (n + 1)) (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (pairsInterpreted : Interprets model (.termEq context first second (.sigma firstDomain firstBody))) :
    Interprets model (.termEq context (.snd firstDomain firstBody first) (.snd secondDomain secondBody second)
      (firstBody.substitute (instantiate (.fst firstDomain firstBody first)))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.secondAnnotationCongruence_sound model.toAbstract (model.stable_toAbstract stable)
      context firstDomain secondDomain firstBody secondBody first second domainsInterpreted.toAbstract
      bodiesInterpreted.toAbstract pairsInterpreted.toAbstract)

theorem sigmaEliminationAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstBody secondBody firstMotive secondMotive : TypeExpr S (n + 1))
    (firstBranch secondBranch : TermExpr S (n + 2)) (firstPair secondPair : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (motivesInterpreted : Interprets model (.typeEq (.snoc context (.sigma firstDomain firstBody)) firstMotive secondMotive))
    (branchesInterpreted : Interprets model (.termEq (.snoc (.snoc context firstDomain) firstBody)
      firstBranch secondBranch (firstMotive.substitute (packSubstitution firstDomain firstBody))))
    (pairsInterpreted : Interprets model (.termEq context firstPair secondPair (.sigma firstDomain firstBody))) :
    Interprets model (.termEq context (.sigmaElim firstDomain firstBody firstMotive firstBranch firstPair)
      (.sigmaElim secondDomain secondBody secondMotive secondBranch secondPair)
        (firstMotive.substitute (instantiate firstPair))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaEliminationAnnotationCongruence_sound model.toAbstract
      (model.stable_toAbstract stable) context firstDomain secondDomain firstBody secondBody firstMotive
      secondMotive firstBranch secondBranch firstPair secondPair domainsInterpreted.toAbstract
      bodiesInterpreted.toAbstract motivesInterpreted.toAbstract branchesInterpreted.toAbstract
      pairsInterpreted.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
