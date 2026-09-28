import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution

/-!
# Substitution of interpreted structural replay

The supplied image certificates are interpreted at their actual substituted
context types. Binder lifting uses the existing certificate weakening, and
its meanings reindex by the corresponding environment projection.

Substituting a product expression for a variable may add product-domain
metadata. Value agreement is unconditional; equality of that metadata is
required when the original subject is itself a product expression.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph sigmaSet)
open ZFSetTraceProducts (traceLam traceApp tracePiSet)
open ZFSetTraceProofDecoding (truthCode)
open Mettapedia.SetTheory

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n m : Nat}

def imageEnvironment (images : Fin n → Meaning.{u} m) (env : Environment.{u} m) : Environment.{u} n :=
  fun index => (images index).value env

/-- Two independently assembled image families give the same value to a
supported expression when their values agree at that expression's free
outer variables. Images at unused context positions need not agree. -/
theorem interpret_imageEnvironment_eq_of_freeVariables
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (term : Tm Head n) (admitted : ZFSetTypeExpressionInterpretation.supported term = true)
    (leftImages rightImages : Fin n → Meaning.{u} m) (env : Environment.{u} m)
    (agreement : ∀ index, index ∈ term.freeVariables →
      (leftImages index).value env = (rightImages index).value env) :
    ZFSetTypeExpressionInterpretation.interpret heads constants term admitted
      (imageEnvironment leftImages env) =
    ZFSetTypeExpressionInterpretation.interpret heads constants term admitted
      (imageEnvironment rightImages env) := by
  exact ZFSetTypeExpressionInterpretation.interpret_eq_of_freeVariables_agree
    heads constants term admitted _ _ agreement

def liftImageMeanings (images : Fin n → Meaning.{u} m) : Fin (n + 1) → Meaning.{u} (m + 1) :=
  Fin.cases (.plain (fun env => env 0)) (fun index => (images index).reindex wk)

theorem imageEnvironment_lift (images : Fin n → Meaning.{u} m)
    (env : Environment.{u} m) (value : ZFSet.{u}) :
    imageEnvironment (liftImageMeanings images) (extend env value) =
      extend (imageEnvironment images env) value := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · change (images prior).value (extend env value ∘ wk) = (images prior).value env
    rfl

theorem assemble_liftVariableCodes
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (context : Ctx Head n) (σ : Sub Head n m) (codes : Fin n → Code Head ConversionCode m)
    (images : Fin n → Meaning.{u} m)
    (assembled : ∀ index, assemble heads constants (codes index) (σ index)
      (subst σ (context.lookup index)) = some (images index)) (A : Tm Head n)
    (index : Fin (n + 1)) :
    assemble heads constants (liftVariableCodes renameConversion codes index) (liftSub σ index)
      (subst (liftSub σ) ((context.snoc A).lookup index)) = some (liftImageMeanings images index) := by
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · simpa only [liftVariableCodes, liftImageMeanings, Fin.cases_succ, liftSub_succ,
      Ctx.lookup, subst_liftSub_wk] using
      assemble_rename renameConversion heads constants (codes prior) (σ prior)
        (subst σ (context.lookup prior)) (images prior) (assembled prior) wk

variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- The existing certificate-substitution algorithm commutes with set values
at every constructor, including lambda bodies and projections. The semantic
image equations are supplied at the context's actual substituted types;
acceptance of the transformed certificate is the separate check_substitute law. -/
theorem assemble_substitute (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject type : Tm Head n} (meaning : Meaning.{u} n),
      check R conversionCheck context subject type code = true →
      assemble heads constants code subject type = some meaning →
      ∀ {m : Nat} (σ : Sub Head n m) (codes : Fin n → Code Head ConversionCode m)
        (images : Fin n → Meaning.{u} m),
        (∀ index, assemble heads constants (codes index) (σ index)
          (subst σ (context.lookup index)) = some (images index)) →
        ∃ result,
          assemble heads constants
            (code.substitute renameConversion substituteConversion σ codes subject type)
            (subst σ subject) (subst σ type) = some result ∧
          (∀ env, result.value env = meaning.value (imageEnvironment images env)) ∧
          (∀ A B, subject = .pi A B → result.productDomain? =
            meaning.productDomain?.map (fun domain env => domain (imageEnvironment images env))) := by
  induction code with
  | headType =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [assemble, Option.some.injEq] at assembled
      subst meaning
      exact ⟨_, rfl, fun _ => rfl, by intros; contradiction⟩
  | var =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> simp only [check, Bool.false_eq_true, decide_eq_true_eq] at accepted
      subst type
      simp only [assemble, Option.some.injEq] at assembled
      subst meaning
      exact ⟨_, atImages _, fun _ => rfl, by intros; contradiction⟩
  | const level formation _ =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [assemble, Option.some.injEq] at assembled
      subst meaning
      exact ⟨_, rfl, fun _ => rfl, by intros; contradiction⟩
  | piForm u v domain body ihA ihB =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨a, atA, b, atB, rfl⟩ := assembled
      obtain ⟨a', atA', valueA, _⟩ := ihA a accepted.1.2 atA σ codes images atImages
      obtain ⟨b', atB', valueB, _⟩ := ihB b accepted.2 atB (liftSub σ)
        (liftVariableCodes renameConversion codes) (liftImageMeanings images)
        (assemble_liftVariableCodes renameConversion heads constants context σ codes images atImages _)
      simp only [subst] at atA' atB'
      refine ⟨⟨fun env => tracePiSet (a'.value env) (fun value => b'.value (extend env value)),
        some a'.value⟩, ?_, ?_, ?_⟩
      · simp [Code.substitute, subst, assemble, atA', atB']
      · intro env
        change tracePiSet _ _ = tracePiSet _ _
        rw [valueA]
        congr 1
        funext value
        rw [valueB, imageEnvironment_lift]
      · intro A B same
        cases same
        simp only [Option.map_some]
        congr 1
        funext env
        exact valueA env
  | sigmaForm u v domain body ihA ihB =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨a, atA, b, atB, rfl⟩ := assembled
      obtain ⟨a', atA', valueA, _⟩ := ihA a accepted.1.2 atA σ codes images atImages
      obtain ⟨b', atB', valueB, _⟩ := ihB b accepted.2 atB (liftSub σ)
        (liftVariableCodes renameConversion codes) (liftImageMeanings images)
        (assemble_liftVariableCodes renameConversion heads constants context σ codes images atImages _)
      simp only [subst] at atA' atB'
      refine ⟨.plain (fun env => sigmaSet (a'.value env) (fun value => b'.value (extend env value))),
        ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atA', atB']
      · intro env
        change sigmaSet _ _ = sigmaSet _ _
        rw [valueA]
        congr 1
        funext value
        rw [valueB, imageEnvironment_lift]
  | lamIntro level formation body ihFormation ihBody =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨formed, atFormation, domain, atDomain, b, atBody, rfl⟩ := assembled
      obtain ⟨formed', atFormation', _, domains⟩ :=
        ihFormation formed accepted.1.2 atFormation σ codes images atImages
      have atDomain' := domains _ _ rfl
      rw [atDomain, Option.map_some] at atDomain'
      obtain ⟨b', atBody', valueB, _⟩ := ihBody b accepted.2 atBody (liftSub σ)
        (liftVariableCodes renameConversion codes) (liftImageMeanings images)
        (assemble_liftVariableCodes renameConversion heads constants context σ codes images atImages _)
      simp only [subst] at atFormation'
      refine ⟨.plain (fun env => traceLam (graph (domain (imageEnvironment images env))
        (fun value => b'.value (extend env value)))), ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atFormation', atDomain', atBody']
      · intro env
        change traceLam (graph _ _) = traceLam (graph _ _)
        congr 2
        funext value
        rw [valueB, imageEnvironment_lift]
  | appElim A B function argument ihF ihA =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨f, atF, a, atA, rfl⟩ := assembled
      obtain ⟨f', atF', valueF, _⟩ := ihF f accepted.1.1 atF σ codes images atImages
      obtain ⟨a', atA', valueA, _⟩ := ihA a accepted.1.2 atA σ codes images atImages
      simp only [subst] at atF'
      refine ⟨.plain (fun env => traceApp (f'.value env) (a'.value env)),
        ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atF', atA']
      · intro env
        change traceApp _ _ = traceApp _ _
        rw [valueF, valueA]
  | pairIntro level formation first second _ ihX ihY =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨x, atX, y, atY, rfl⟩ := assembled
      obtain ⟨x', atX', valueX, _⟩ := ihX x accepted.1.2 atX σ codes images atImages
      obtain ⟨y', atY', valueY, _⟩ := ihY y accepted.2 atY σ codes images atImages
      rw [subst_inst0] at atY'
      refine ⟨.plain (fun env => ZFSet.pair (x'.value env) (y'.value env)),
        ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atX', atY']
      · intro env
        change ZFSet.pair _ _ = ZFSet.pair _ _
        rw [valueX, valueY]
  | fstElim B pair ihPair =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨p, atP, rfl⟩ := assembled
      obtain ⟨p', atP', valueP, _⟩ := ihPair p accepted atP σ codes images atImages
      simp only [subst] at atP'
      refine ⟨.plain (fun env => ZFSetOrderedPair.first (p'.value env)),
        ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atP']
      · intro env
        change ZFSetOrderedPair.first _ = ZFSetOrderedPair.first _
        rw [valueP]
  | sndElim A B pair ihPair =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨p, atP, rfl⟩ := assembled
      obtain ⟨p', atP', valueP, _⟩ := ihPair p accepted.1 atP σ codes images atImages
      simp only [subst] at atP'
      refine ⟨.plain (fun env => ZFSetOrderedPair.second (p'.value env)),
        ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atP']
      · intro env
        change ZFSetOrderedPair.second _ = ZFSetOrderedPair.second _
        rw [valueP]
  | idForm level formation left right _ ihX ihY =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨x, atX, y, atY, rfl⟩ := assembled
      obtain ⟨x', atX', valueX, _⟩ := ihX x accepted.1.1.2 atX σ codes images atImages
      obtain ⟨y', atY', valueY, _⟩ := ihY y accepted.1.2 atY σ codes images atImages
      refine ⟨.plain (fun env => truthCode (x'.value env = y'.value env)),
        ?_, ?_, by intros; contradiction⟩
      · simp [Code.substitute, subst, assemble, atX', atY']
      · intro env
        change truthCode (_ = _) = truthCode (_ = _)
        rw [valueX, valueY]
  | reflIntro A term _ =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [assemble, Option.some.injEq] at assembled
      subst meaning
      exact ⟨_, rfl, fun _ => rfl, by intros; contradiction⟩
  | cumul level source ih =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      simpa only [Code.substitute, subst, assemble] using
        ih meaning accepted.1 assembled σ codes images atImages
  | convert A level source formation conversion ih _ =>
      intro context subject type meaning accepted assembled m σ codes images atImages
      simp only [check, Bool.and_eq_true] at accepted
      simpa only [Code.substitute, assemble] using
        ih meaning accepted.1.1.2 assembled σ codes images atImages

/-- Two actual certificate substitutions preserve a relation indexed by the
source environments induced by their respective images. The relation may
therefore mention dependent type fibres or retained function domains, rather
than being a fixed relation on untyped result values. -/
theorem assemble_substitute_indexed_related
    (leftContext rightContext : Ctx Head n)
    (leftSubject leftType rightSubject rightType : Tm Head n)
    (leftCode rightCode : Code Head ConversionCode n)
    (left right : Meaning.{u} n)
    (leftChecked : check R conversionCheck leftContext leftSubject leftType leftCode = true)
    (rightChecked : check R conversionCheck rightContext rightSubject rightType rightCode = true)
    (atLeft : assemble heads constants leftCode leftSubject leftType = some left)
    (atRight : assemble heads constants rightCode rightSubject rightType = some right)
    (leftSub rightSub : Sub Head n m)
    (leftImages rightImages : Fin n → Code Head ConversionCode m)
    (leftMeanings rightMeanings : Fin n → Meaning.{u} m)
    (atLeftImages : ∀ i, assemble heads constants (leftImages i) (leftSub i)
      (subst leftSub (leftContext.lookup i)) = some (leftMeanings i))
    (atRightImages : ∀ i, assemble heads constants (rightImages i) (rightSub i)
      (subst rightSub (rightContext.lookup i)) = some (rightMeanings i))
    (sourceRelation : Environment.{u} n → Environment.{u} n → Prop)
    (targetRelation : Environment.{u} m → Environment.{u} m → Prop)
    (outputRelation : Environment.{u} n → Environment.{u} n →
      ZFSet.{u} → ZFSet.{u} → Prop)
    (sourcesRelated : ∀ leftEnv rightEnv, sourceRelation leftEnv rightEnv →
      outputRelation leftEnv rightEnv (left.value leftEnv) (right.value rightEnv))
    (imagesRelated : ∀ leftEnv rightEnv, targetRelation leftEnv rightEnv →
      sourceRelation (imageEnvironment leftMeanings leftEnv)
        (imageEnvironment rightMeanings rightEnv)) :
    ∃ leftResult rightResult,
      assemble heads constants
        (leftCode.substitute renameConversion substituteConversion leftSub leftImages
          leftSubject leftType)
        (subst leftSub leftSubject) (subst leftSub leftType) = some leftResult ∧
      assemble heads constants
        (rightCode.substitute renameConversion substituteConversion rightSub rightImages
          rightSubject rightType)
        (subst rightSub rightSubject) (subst rightSub rightType) = some rightResult ∧
      (∀ env, leftResult.value env =
        left.value (imageEnvironment leftMeanings env)) ∧
      (∀ env, rightResult.value env =
        right.value (imageEnvironment rightMeanings env)) ∧
      ∀ leftEnv rightEnv, targetRelation leftEnv rightEnv →
        outputRelation (imageEnvironment leftMeanings leftEnv)
          (imageEnvironment rightMeanings rightEnv)
          (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  obtain ⟨leftResult, leftAssembled, leftValues, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      leftCode left leftChecked atLeft leftSub leftImages leftMeanings atLeftImages
  obtain ⟨rightResult, rightAssembled, rightValues, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      rightCode right rightChecked atRight rightSub rightImages rightMeanings atRightImages
  refine ⟨leftResult, rightResult, leftAssembled, rightAssembled,
    leftValues, rightValues, ?_⟩
  intro leftEnv rightEnv related
  rw [leftValues, rightValues]
  exact sourcesRelated _ _ (imagesRelated leftEnv rightEnv related)

/-- Opening one binder interprets the actual instantiated certificate at the
environment extended by the argument value. Nested lambdas and projections
are included; no structural-fragment support test is needed. -/
theorem assemble_instantiate {context : Ctx Head n} {A argument : Tm Head n}
    {subject type : Tm Head (n + 1)}
    (bodyCode : Code Head ConversionCode (n + 1)) (argumentCode : Code Head ConversionCode n)
    (bodyMeaning : Meaning.{u} (n + 1)) (argumentMeaning : Meaning.{u} n)
    (accepted : check R conversionCheck (.snoc context A) subject type bodyCode = true)
    (atBody : assemble heads constants bodyCode subject type = some bodyMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some argumentMeaning) :
    ∃ result, assemble heads constants
        (Code.instantiate renameConversion substituteConversion subject type argument bodyCode argumentCode)
        (inst0 argument subject) (inst0 argument type) = some result ∧
      ∀ env, result.value env = bodyMeaning.value (extend env (argumentMeaning.value env)) := by
  let images : Fin (n + 1) → Meaning.{u} n :=
    Fin.cases argumentMeaning (fun index => .plain (fun env => env index))
  have atImages : ∀ index, assemble heads constants
      (Fin.cases argumentCode (fun _ => .var) index) (consSub argument ids index)
      (subst (consSub argument ids) ((context.snoc A).lookup index)) = some (images index) := by
    intro index
    refine Fin.cases ?_ (fun prior => ?_) index
    · simpa only [consSub, Fin.cases_zero, Ctx.lookup_snoc_zero,
        subst_consSub_rename_wk, subst_ids, images] using atArgument
    · rfl
  obtain ⟨result, assembled, values, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      bodyCode bodyMeaning accepted atBody (consSub argument ids)
      (Fin.cases argumentCode (fun _ => .var)) images atImages
  refine ⟨result, assembled, ?_⟩
  intro env
  rw [values]
  congr 1
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

#print axioms assemble_substitute
#print axioms assemble_substitute_indexed_related
#print axioms interpret_imageEnvironment_eq_of_freeVariables
#print axioms assemble_instantiate
#print axioms imageEnvironment_lift
#print axioms assemble_liftVariableCodes

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
