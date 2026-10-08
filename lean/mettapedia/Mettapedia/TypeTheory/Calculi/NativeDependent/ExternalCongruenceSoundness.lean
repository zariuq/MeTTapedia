import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalStructuralSoundness

/-!
# Annotation-sensitive constructor equations in dependent models

Converted domain, codomain and full-motive annotations are interpreted by
the same actual model data. The constructor equations follow from evaluating
their supplied term equations at those shared dependent types. Primitive
argument equations retain their actual dependent telescope arrows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}} {D : Signature S}

namespace ModelData

variable (model : ModelData S C) {n : Nat}

theorem piCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody)) :
    Interprets model (.typeEq context (.pi firstDomain firstBody) (.pi secondDomain secondBody)) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  exact ⟨Γ, model.products.pi A B, contextRead,
    model.evaluate_pi Γ firstDomain firstBody A B firstDomainRead firstBodyRead,
    model.evaluate_pi Γ secondDomain secondBody A B secondDomainRead secondBodyRead⟩

theorem sigmaCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody)) :
    Interprets model (.typeEq context (.sigma firstDomain firstBody) (.sigma secondDomain secondBody)) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  exact ⟨Γ, model.sums.operations.sigma A B, contextRead,
    model.evaluate_sigma Γ firstDomain firstBody A B firstDomainRead firstBodyRead,
    model.evaluate_sigma Γ secondDomain secondBody A B secondDomainRead secondBodyRead⟩

theorem familyCongruence_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (first second : Substitution S (S.typeArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.typeParameters symbol) first second)) :
    Interprets model (.typeEq context (.family symbol first) (.family symbol second)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans (realization.typeHeader symbol))
  exact ⟨Γ, model.familyAt symbol σ, contextRead,
    model.evaluate_family Γ symbol first σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead),
    model.evaluate_family Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem primitiveCongruence_sound (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (first second : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.termParameters symbol) first second)) :
    Interprets model (.termEq context (.primitive symbol first) (.primitive symbol second)
      ((D.termResult symbol).substitute first)) := by
  rcases argumentsInterpreted with ⟨Γ, actual, σ, contextRead, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans (realization.termHeader symbol))
  let firstMap := ModelSubstitution.ofEvaluated model Γ (model.termParameters symbol) first σ firstRead
  exact ⟨Γ, (model.primitiveAt symbol σ).1, (model.primitiveAt symbol σ).2, contextRead,
    model.evaluateType_substitute stable (D.termResult symbol) Γ (model.termParameters symbol)
      first firstMap _ (realization.termResult symbol),
    model.evaluate_primitive Γ symbol first σ firstMap.readout,
    model.evaluate_primitive Γ symbol second σ ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem lambdaAnnotationCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (first second : TermExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (termsInterpreted : Interprets model (.termEq (.snoc context firstDomain) first second firstBody)) :
    Interprets model (.termEq context (.lam firstDomain firstBody first) (.lam secondDomain secondBody second)
      (.pi firstDomain firstBody)) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  rcases termsInterpreted.termEqAt (Γ.snoc A) B
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead) firstBodyRead with
    ⟨value, firstRead, secondRead⟩
  exact ⟨Γ, _, model.products.lam value, contextRead,
    model.evaluate_pi Γ firstDomain firstBody A B firstDomainRead firstBodyRead,
    model.evaluate_lambda Γ firstDomain firstBody A B firstDomainRead firstBodyRead first value firstRead,
    model.evaluate_lambda Γ secondDomain secondBody A B secondDomainRead secondBodyRead second value secondRead⟩

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
        (firstBody.substitute (instantiate firstArgument))) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  rcases functionsInterpreted.termEqAt Γ _ contextRead
    (model.evaluate_pi Γ firstDomain firstBody A B firstDomainRead firstBodyRead) with ⟨f, firstFunctionRead, secondFunctionRead⟩
  rcases argumentsInterpreted.termEqAt Γ A contextRead firstDomainRead with ⟨a, firstArgumentRead, secondArgumentRead⟩
  exact ⟨Γ, _, model.products.app f a, contextRead,
    model.evaluateType_instantiate stable Γ A firstBody B firstArgument a firstBodyRead firstArgumentRead,
    model.evaluate_application Γ firstDomain firstBody A B firstDomainRead firstBodyRead
      firstFunction firstArgument f a firstFunctionRead firstArgumentRead,
    model.evaluate_application Γ secondDomain secondBody A B secondDomainRead secondBodyRead
      secondFunction secondArgument f a secondFunctionRead secondArgumentRead⟩

theorem pairAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstBody secondBody : TypeExpr S (n + 1)) (firstLeft secondLeft firstRight secondRight : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (firstInterpreted : Interprets model (.termEq context firstLeft secondLeft firstDomain))
    (secondInterpreted : Interprets model (.termEq context firstRight secondRight (firstBody.substitute (instantiate firstLeft)))) :
    Interprets model (.termEq context (.pair firstDomain firstBody firstLeft firstRight)
      (.pair secondDomain secondBody secondLeft secondRight) (.sigma firstDomain firstBody)) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  rcases firstInterpreted.termEqAt Γ A contextRead firstDomainRead with ⟨a, firstLeftRead, secondLeftRead⟩
  rcases secondInterpreted.termEqAt Γ _ contextRead
    (model.evaluateType_instantiate stable Γ A firstBody B firstLeft a firstBodyRead firstLeftRead) with
    ⟨b, firstRightRead, secondRightRead⟩
  exact ⟨Γ, _, model.sums.operations.pair a b, contextRead,
    model.evaluate_sigma Γ firstDomain firstBody A B firstDomainRead firstBodyRead,
    model.evaluate_pair Γ firstDomain firstBody A B firstDomainRead firstBodyRead
      firstLeft firstRight a b firstLeftRead firstRightRead,
    model.evaluate_pair Γ secondDomain secondBody A B secondDomainRead secondBodyRead
      secondLeft secondRight a b secondLeftRead secondRightRead⟩

theorem firstAnnotationCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstBody secondBody : TypeExpr S (n + 1))
    (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (pairsInterpreted : Interprets model (.termEq context first second (.sigma firstDomain firstBody))) :
    Interprets model (.termEq context (.fst firstDomain firstBody first) (.fst secondDomain secondBody second) firstDomain) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  rcases pairsInterpreted.termEqAt Γ _ contextRead
    (model.evaluate_sigma Γ firstDomain firstBody A B firstDomainRead firstBodyRead) with ⟨p, firstRead, secondRead⟩
  exact ⟨Γ, A, model.sums.operations.fst p, contextRead, firstDomainRead,
    model.evaluate_first Γ firstDomain firstBody A B firstDomainRead firstBodyRead first p firstRead,
    model.evaluate_first Γ secondDomain secondBody A B secondDomainRead secondBodyRead second p secondRead⟩

theorem secondAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstBody secondBody : TypeExpr S (n + 1)) (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody))
    (pairsInterpreted : Interprets model (.termEq context first second (.sigma firstDomain firstBody))) :
    Interprets model (.termEq context (.snd firstDomain firstBody first) (.snd secondDomain secondBody second)
      (firstBody.substitute (instantiate (.fst firstDomain firstBody first)))) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  rcases pairsInterpreted.termEqAt Γ _ contextRead
    (model.evaluate_sigma Γ firstDomain firstBody A B firstDomainRead firstBodyRead) with ⟨p, firstRead, secondRead⟩
  exact ⟨Γ, _, model.sums.operations.snd p, contextRead,
    model.evaluateType_instantiate stable Γ A firstBody B (.fst firstDomain firstBody first)
      (model.sums.operations.fst p) firstBodyRead
      (model.evaluate_first Γ firstDomain firstBody A B firstDomainRead firstBodyRead first p firstRead),
    model.evaluate_second Γ firstDomain firstBody A B firstDomainRead firstBodyRead first p firstRead,
    model.evaluate_second Γ secondDomain secondBody A B secondDomainRead secondBodyRead second p secondRead⟩

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
        (firstMotive.substitute (instantiate firstPair))) := by
  rcases Interprets.dependentTypeEquations domainsInterpreted bodiesInterpreted with
    ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩
  have sumRead := model.evaluate_sigma Γ firstDomain firstBody A B firstDomainRead firstBodyRead
  have sumContextRead := model.evaluateContext_snoc context (.sigma firstDomain firstBody) Γ _ contextRead sumRead
  rcases motivesInterpreted with ⟨actual, M, actualRead, firstMotiveRead, secondMotiveRead⟩
  cases Option.some.inj (actualRead.symm.trans sumContextRead)
  have tupleContextRead := model.evaluateContext_snoc (.snoc context firstDomain) firstBody (Γ.snoc A) B
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead) firstBodyRead
  have branchTypeRead := model.evaluateType_substitute stable firstMotive ((Γ.snoc A).snoc B)
    (Γ.snoc (model.sums.operations.sigma A B)) (packSubstitution firstDomain firstBody)
    (ModelSubstitution.packPair stable Γ firstDomain firstBody A B firstDomainRead firstBodyRead) M firstMotiveRead
  rcases branchesInterpreted.termEqAt ((Γ.snoc A).snoc B) _ tupleContextRead branchTypeRead with
    ⟨b, firstBranchRead, secondBranchRead⟩
  rcases pairsInterpreted.termEqAt Γ _ contextRead sumRead with ⟨p, firstPairRead, secondPairRead⟩
  exact ⟨Γ, _, C.toCwf.tmSub (eliminate model.sums A B M b) (selfExtend C.toCwf p), contextRead,
    model.evaluateType_instantiate stable Γ (model.sums.operations.sigma A B) firstMotive M firstPair p firstMotiveRead firstPairRead,
    model.evaluate_sumElimination Γ firstDomain firstBody A B firstDomainRead firstBodyRead
      firstMotive firstBranch firstPair M b p firstMotiveRead firstBranchRead firstPairRead,
    model.evaluate_sumElimination Γ secondDomain secondBody A B secondDomainRead secondBodyRead
      secondMotive secondBranch secondPair M b p secondMotiveRead secondBranchRead secondPairRead⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
