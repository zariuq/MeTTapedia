import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayNeutralCoherence

/-!
# Comparing the environments of retained context certificates

Agreement of a new type is needed only over valid prior environments. This
is sufficient to identify the actual predicates assembled for context
extension, even if the type values differ on invalid raw environments.

For telescopes whose supplied type certificates have neutral eliminations,
the comparison premise is discharged by the existing certificate-independence
theorem. The second accepted context certificate is unrestricted within the
no-conversion profile. No uniqueness of typing certificates is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type}

/-- Apply the existing neutral-elimination qualification to each actual
type-formation tree in a supplied telescope certificate. -/
def ContextCode.neutralFormations : {n : Nat} →
    ContextCode Head NoConversion n → Ctx Head n → Bool
  | _, .nil, .nil => true
  | _, .snoc prior level formation, .snoc context A =>
      prior.neutralFormations context && formation.neutralEliminations A (.head level)

end StructuralTypingReplay

namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- The concrete extension predicates agree when their prior contexts agree
and the new type values agree on those valid environments. Values outside
that domain are neither compared nor used to authorize a context member. -/
theorem assembleContext_extensions_eq
    (firstContext secondContext : Ctx Head n) (A B : Tm Head n)
    (first second : ContextCode Head ConversionCode n) (firstLevel secondLevel : Head)
    (firstFormation secondFormation : Code Head ConversionCode n)
    (firstValid secondValid : Environment.{u} n → Prop)
    (firstType secondType : Meaning.{u} n)
    (firstExtended secondExtended : Environment.{u} (n + 1) → Prop)
    (atFirst : assembleContext heads constants first firstContext = some firstValid)
    (atSecond : assembleContext heads constants second secondContext = some secondValid)
    (atFirstType : assemble heads constants firstFormation A (.head firstLevel) = some firstType)
    (atSecondType : assemble heads constants secondFormation B (.head secondLevel) = some secondType)
    (atFirstExtended : assembleContext heads constants (.snoc first firstLevel firstFormation)
      (.snoc firstContext A) = some firstExtended)
    (atSecondExtended : assembleContext heads constants (.snoc second secondLevel secondFormation)
      (.snoc secondContext B) = some secondExtended)
    (priorAgree : ∀ env, firstValid env ↔ secondValid env)
    (typeAgree : ∀ env, firstValid env → firstType.value env = secondType.value env) :
    firstExtended = secondExtended := by
  simp only [assembleContext, atFirst, atFirstType, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at atFirstExtended
  simp only [assembleContext, atSecond, atSecondType, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at atSecondExtended
  subst firstExtended
  subst secondExtended
  funext env
  apply propext
  constructor
  · rintro ⟨valid, member⟩
    exact ⟨(priorAgree _).mp valid, (typeAgree _ valid) ▸ member⟩
  · rintro ⟨valid, member⟩
    have prior := (priorAgree _).mpr valid
    exact ⟨prior, (typeAgree _ prior).symm ▸ member⟩

/-- The same raw telescope may be assembled using independent certificates.
This is the same-syntax specialization of `assembleContext_extensions_eq`. -/
theorem assembleContext_extension_eq
    (context : Ctx Head n) (A : Tm Head n)
    (first second : ContextCode Head ConversionCode n) (firstLevel secondLevel : Head)
    (firstFormation secondFormation : Code Head ConversionCode n)
    (firstValid secondValid : Environment.{u} n → Prop)
    (firstType secondType : Meaning.{u} n)
    (firstExtended secondExtended : Environment.{u} (n + 1) → Prop)
    (atFirst : assembleContext heads constants first context = some firstValid)
    (atSecond : assembleContext heads constants second context = some secondValid)
    (atFirstType : assemble heads constants firstFormation A (.head firstLevel) = some firstType)
    (atSecondType : assemble heads constants secondFormation A (.head secondLevel) = some secondType)
    (atFirstExtended : assembleContext heads constants (.snoc first firstLevel firstFormation)
      (.snoc context A) = some firstExtended)
    (atSecondExtended : assembleContext heads constants (.snoc second secondLevel secondFormation)
      (.snoc context A) = some secondExtended)
    (priorAgree : ∀ env, firstValid env ↔ secondValid env)
    (typeAgree : ∀ env, firstValid env → firstType.value env = secondType.value env) :
    firstExtended = secondExtended :=
  assembleContext_extensions_eq heads constants context context A A first second
    firstLevel secondLevel firstFormation secondFormation firstValid secondValid firstType secondType
    firstExtended secondExtended atFirst atSecond atFirstType atSecondType atFirstExtended
    atSecondExtended priorAgree typeAgree

/-- Changing a qualified context certificate leaves the environment itself
unchanged. Only its proof of membership is transported. -/
def environmentEquiv {first second : Environment.{u} n → Prop}
    (agreement : ∀ env, first env ↔ second env) :
    {env // first env} ≃ {env // second env} where
  toFun env := ⟨env.1, (agreement _).mp env.2⟩
  invFun env := ⟨env.1, (agreement _).mpr env.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The comparison commutes with weakening on an extended environment. -/
theorem environmentEquiv_weakening {first second : Environment.{u} (n + 1) → Prop}
    (agreement : ∀ env, first env ↔ second env) (env : {env // first env}) :
    (environmentEquiv agreement env).1 ∘ wk = env.1 ∘ wk := rfl

/-- The comparison retains the actual newest variable, including its proof
value when the new family is an identity type. -/
theorem environmentEquiv_variable {first second : Environment.{u} (n + 1) → Prop}
    (agreement : ∀ env, first env ↔ second env) (env : {env // first env}) :
    (environmentEquiv agreement env).1 0 = env.1 0 := rfl

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- A telescope with qualified formation certificates has exactly the same
valid environments as every other accepted certificate for that telescope.
Formation levels and cumulative wrappers may differ. -/
theorem assembleContext_neutralFormations_coherent {n : Nat}
    (first : ContextCode Head NoConversion n) :
    ∀ {context : Ctx Head n} {second : ContextCode Head NoConversion n}
      {firstValid secondValid : Environment.{u} n → Prop},
      checkContext R noConversionCheck context first = true →
      first.neutralFormations context = true →
      assembleContext heads constants first context = some firstValid →
      checkContext R noConversionCheck context second = true →
      assembleContext heads constants second context = some secondValid →
      firstValid = secondValid := by
  induction first with
  | nil =>
      intro context second firstValid secondValid _ _ atFirst _ atSecond
      cases context
      cases second
      exact Option.some.inj (atFirst.symm.trans atSecond)
  | snoc prior level formation ih =>
      intro context second firstValid secondValid checked qualified atFirst otherChecked atSecond
      cases context with
      | snoc context A =>
          cases second with
          | snoc other otherLevel otherFormation =>
              simp only [checkContext, Bool.and_eq_true] at checked otherChecked
              simp only [ContextCode.neutralFormations, Bool.and_eq_true] at qualified
              simp only [assembleContext, Option.bind_eq_bind, Option.bind_eq_some_iff,
                Option.pure_def, Option.some.injEq] at atFirst atSecond
              obtain ⟨valid, atValid, type, atType, rfl⟩ := atFirst
              obtain ⟨otherValid, atOtherValid, otherType, atOtherType, rfl⟩ := atSecond
              cases ih checked.1.1 qualified.1 atValid otherChecked.1.1 atOtherValid
              cases assemble_neutralEliminations_coherent heads constants R formation
                checked.2 qualified.2 atType otherChecked.2 atOtherType
                (EqualOrHeads.heads level otherLevel)
              rfl

#print axioms assembleContext_extensions_eq
#print axioms assembleContext_extension_eq
#print axioms assembleContext_neutralFormations_coherent
#print axioms environmentEquiv

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
