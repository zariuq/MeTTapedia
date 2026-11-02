import Mettapedia.Logic.HOL.CurriedPredicates

/-!
# Retained proofs for curried field predicates

Constant and conjunction predicates reduce by explicit beta proofs. Their
introduction operations consume the original premise proofs and retain every
inference. Substitution laws apply to the actual generated predicate syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.CurriedPredicates
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base}

theorem constant_natural (fields : List (Ty Base)) (formula : Formula Const Γ) :
    NaturalBody (fields := fields) (fun rho _ => HOL.subst rho formula) := by
  intro earlierContext laterContext earlier later arguments
  exact HOL.subst_comp later earlier formula

theorem conjoin_natural (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields)) :
    NaturalBody (fun rho arguments => Term.and
      (applyArguments fields (HOL.subst rho first) arguments)
      (applyArguments fields (HOL.subst rho second) arguments)) := by
  intro earlierContext laterContext earlier later arguments
  simp only [HOL.subst, applyArguments_subst, HOL.subst_comp]
  rfl

theorem constant_subst (rho : Subst Const Γ Δ) (fields : List (Ty Base)) (formula : Formula Const Γ) :
    HOL.subst rho (constant fields formula) = constant fields (HOL.subst rho formula) := by
  unfold constant
  rw [abstractArguments_subst rho fields _ (constant_natural fields formula)]
  apply congrArg (abstractArguments fields)
  funext laterContext later arguments
  exact (HOL.subst_comp later rho formula).symm

theorem conjoin_subst (rho : Subst Const Γ Δ) (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields)) :
    HOL.subst rho (conjoin fields first second) =
      conjoin fields (HOL.subst rho first) (HOL.subst rho second) := by
  unfold conjoin
  rw [abstractArguments_subst rho fields _ (conjoin_natural fields first second)]
  apply congrArg (abstractArguments fields)
  funext laterContext later arguments
  simp only [HOL.subst_comp]
  rfl

theorem equalTo_natural {result : Ty Base} (fields : List (Ty Base))
    (function : Term Const Γ (FunctionType fields result)) (expected : Term Const Γ result) :
    NaturalBody (fun rho arguments => Term.eq
      (applyFields fields (HOL.subst rho function) arguments) (HOL.subst rho expected)) := by
  intro earlierContext laterContext earlier later arguments
  simp only [HOL.subst, applyFields_subst, HOL.subst_comp]
  rfl

def constant_beta {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (formula : Formula Const Γ) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions (.eq (applyArguments fields (constant fields formula) arguments) formula) := by
  have generated := abstractArguments_beta (assumptions := assumptions) fields
    (fun rho _ => HOL.subst rho formula) (constant_natural fields formula) arguments
  apply ProofSyntax.castIndices rfl ?_ generated
  exact congrArg (Term.eq _) (HOL.subst_id formula)

def conjoin_beta {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields)) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions (.eq (applyArguments fields (conjoin fields first second) arguments)
      (.and (applyArguments fields first arguments) (applyArguments fields second arguments))) := by
  have generated := abstractArguments_beta (assumptions := assumptions) fields
    (fun rho args => Term.and (applyArguments fields (HOL.subst rho first) args)
      (applyArguments fields (HOL.subst rho second) args)) (conjoin_natural fields first second) arguments
  apply ProofSyntax.castIndices rfl ?_ generated
  apply congrArg (Term.eq _)
  exact congrArg₂ Term.and
    (congrArg (fun condition => applyArguments fields condition arguments) (HOL.subst_id first))
    (congrArg (fun condition => applyArguments fields condition arguments) (HOL.subst_id second))

def equalTo_beta {assumptions : List (Formula Const Γ)} {result : Ty Base}
    (fields : List (Ty Base)) (function : Term Const Γ (FunctionType fields result))
    (expected : Term Const Γ result) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions (.eq (applyArguments fields (equalTo fields function expected) arguments)
      (.eq (applyFields fields function arguments) expected)) := by
  have generated := abstractArguments_beta (assumptions := assumptions) fields
    (fun rho args => Term.eq (applyFields fields (HOL.subst rho function) args) (HOL.subst rho expected))
    (equalTo_natural fields function expected) arguments
  apply ProofSyntax.castIndices rfl ?_ generated
  apply congrArg (Term.eq _)
  exact congrArg₂ Term.eq
    (congrArg (fun term => applyFields fields term arguments) (HOL.subst_id function)) (HOL.subst_id expected)

def applyFields_congr {assumptions : List (Formula Const Γ)} {result : Ty Base}
    (fields : List (Ty Base)) (first second : Term Const Γ (FunctionType fields result))
    (arguments : Arguments Const Γ fields) (proof : ProofSyntax Const assumptions (.eq first second)) :
    ProofSyntax Const assumptions (.eq (applyFields fields first arguments) (applyFields fields second arguments)) := by
  induction fields with
  | nil => exact proof
  | cons type rest hypothesis =>
      exact hypothesis (.app first arguments.1) (.app second arguments.1) arguments.2 (.eqApp arguments.1 proof)

def applyFields_beta {assumptions : List (Formula Const Γ)} {domain result : Ty Base}
    (fields : List (Ty Base)) (body : Term Const (domain :: Γ) (FunctionType fields result))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions (.eq (applyFields (domain :: fields) (.lam body) (argument, arguments))
      (applyFields fields (instantiate argument body) arguments)) :=
  applyFields_congr fields _ _ arguments (.beta argument body)

def constant_intro {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    {formula : Formula Const Γ} (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions formula) :
    ProofSyntax Const assumptions (applyArguments fields (constant fields formula) arguments) :=
  .impE (.eqPropER (constant_beta fields formula arguments)) proof

def conjoin_intro {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    {first second : Term Const Γ (handlerType fields)} (arguments : Arguments Const Γ fields)
    (firstProof : ProofSyntax Const assumptions (applyArguments fields first arguments))
    (secondProof : ProofSyntax Const assumptions (applyArguments fields second arguments)) :
    ProofSyntax Const assumptions (applyArguments fields (conjoin fields first second) arguments) :=
  .impE (.eqPropER (conjoin_beta fields first second arguments)) (.andI firstProof secondProof)

def equalTo_intro {assumptions : List (Formula Const Γ)} {result : Ty Base}
    (fields : List (Ty Base)) (function : Term Const Γ (FunctionType fields result))
    (expected : Term Const Γ result) (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (.eq (applyFields fields function arguments) expected)) :
    ProofSyntax Const assumptions (applyArguments fields (equalTo fields function expected) arguments) :=
  .impE (.eqPropER (equalTo_beta fields function expected arguments)) proof

def applyLam_intro {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (applyArguments fields (instantiate argument body) arguments)) :
    ProofSyntax Const assumptions (applyArguments (domain :: fields) (.lam body) (argument, arguments)) :=
  .impE (.eqPropER (applyArguments_congr fields _ _ arguments (.beta argument body))) proof

theorem instantiate_head_body {domain : Ty Base} (fields : List (Ty Base))
    (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields)) (argument : Term Const Γ domain) :
    instantiate argument (conjoin fields
      (constant fields (.app (weaken predicate) (.var .vz))) body) =
      conjoin fields (constant fields (.app predicate argument)) (instantiate argument body) := by
  unfold instantiate
  rw [conjoin_subst, constant_subst]
  apply congrArg (fun formula => conjoin fields (constant fields formula) (HOL.subst (Subst.single argument) body))
  change Term.app (instantiate argument (weaken predicate)) argument = Term.app predicate argument
  rw [instantiate_weaken]

def head_intro {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (headProof : ProofSyntax Const assumptions (.app predicate argument))
    (tailProof : ProofSyntax Const assumptions (applyArguments fields (instantiate argument body) arguments)) :
    ProofSyntax Const assumptions (applyArguments (domain :: fields)
      (.lam (conjoin fields (constant fields (.app (weaken predicate) (.var .vz))) body)) (argument, arguments)) := by
  apply applyLam_intro fields _ argument arguments
  have combined := conjoin_intro fields arguments (constant_intro fields arguments headProof) tailProof
  exact ProofSyntax.castIndices rfl
    (congrArg (fun term => applyArguments fields term arguments) (instantiate_head_body fields predicate body argument).symm) combined

theorem constant_beta_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (formula : Formula Const Γ) (arguments : Arguments Const Γ fields) :
    (constant_beta (assumptions := assumptions) fields formula arguments).FunctionExtensionalityFree := by
  unfold constant_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

theorem conjoin_beta_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields)) (arguments : Arguments Const Γ fields) :
    (conjoin_beta (assumptions := assumptions) fields first second arguments).FunctionExtensionalityFree := by
  unfold conjoin_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

theorem equalTo_beta_free {assumptions : List (Formula Const Γ)} {result : Ty Base}
    (fields : List (Ty Base)) (function : Term Const Γ (FunctionType fields result))
    (expected : Term Const Γ result) (arguments : Arguments Const Γ fields) :
    (equalTo_beta (assumptions := assumptions) fields function expected arguments).FunctionExtensionalityFree := by
  unfold equalTo_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

theorem applyFields_congr_free {assumptions : List (Formula Const Γ)} {result : Ty Base}
    (fields : List (Ty Base)) (first second : Term Const Γ (FunctionType fields result))
    (arguments : Arguments Const Γ fields) (proof : ProofSyntax Const assumptions (.eq first second))
    (free : proof.FunctionExtensionalityFree) :
    (applyFields_congr fields first second arguments proof).FunctionExtensionalityFree := by
  induction fields with
  | nil => exact free
  | cons type rest hypothesis =>
      exact hypothesis (.app first arguments.1) (.app second arguments.1) arguments.2
        (.eqApp arguments.1 proof) free

theorem applyFields_beta_free {assumptions : List (Formula Const Γ)} {domain result : Ty Base}
    (fields : List (Ty Base)) (body : Term Const (domain :: Γ) (FunctionType fields result))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields) :
    (applyFields_beta (assumptions := assumptions) fields body argument arguments).FunctionExtensionalityFree :=
  applyFields_congr_free fields _ _ arguments _ True.intro

theorem constant_intro_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    {formula : Formula Const Γ} (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions formula) (free : proof.FunctionExtensionalityFree) :
    (constant_intro fields arguments proof).FunctionExtensionalityFree := by
  simp only [constant_intro, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨constant_beta_free _ _ _, free⟩

theorem conjoin_intro_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    {first second : Term Const Γ (handlerType fields)} (arguments : Arguments Const Γ fields)
    (firstProof : ProofSyntax Const assumptions (applyArguments fields first arguments))
    (secondProof : ProofSyntax Const assumptions (applyArguments fields second arguments))
    (firstFree : firstProof.FunctionExtensionalityFree) (secondFree : secondProof.FunctionExtensionalityFree) :
    (conjoin_intro fields arguments firstProof secondProof).FunctionExtensionalityFree := by
  simp only [conjoin_intro, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨conjoin_beta_free _ _ _ _, firstFree, secondFree⟩

theorem equalTo_intro_free {assumptions : List (Formula Const Γ)} {result : Ty Base}
    (fields : List (Ty Base)) (function : Term Const Γ (FunctionType fields result))
    (expected : Term Const Γ result) (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (.eq (applyFields fields function arguments) expected))
    (free : proof.FunctionExtensionalityFree) :
    (equalTo_intro fields function expected arguments proof).FunctionExtensionalityFree := by
  simp only [equalTo_intro, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨equalTo_beta_free _ _ _ _, free⟩

theorem applyLam_intro_free {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (applyArguments fields (instantiate argument body) arguments))
    (free : proof.FunctionExtensionalityFree) :
    (applyLam_intro fields body argument arguments proof).FunctionExtensionalityFree := by
  simp only [applyLam_intro, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨applyArguments_congr_free fields _ _ arguments _ True.intro, free⟩

theorem head_intro_free {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (headProof : ProofSyntax Const assumptions (.app predicate argument))
    (tailProof : ProofSyntax Const assumptions (applyArguments fields (instantiate argument body) arguments))
    (headFree : headProof.FunctionExtensionalityFree) (tailFree : tailProof.FunctionExtensionalityFree) :
    (head_intro fields predicate body argument arguments headProof tailProof).FunctionExtensionalityFree := by
  unfold head_intro
  apply applyLam_intro_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact conjoin_intro_free fields arguments _ _ (constant_intro_free fields arguments _ headFree) tailFree

#print axioms constant_subst
#print axioms conjoin_subst
#print axioms conjoin_intro_free
end Mettapedia.Logic.HOL.CurriedPredicates
