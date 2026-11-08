import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionBudget
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Checking

/-!
# Independently typed normal forms belong to the checking fragment

The raw checker is incomplete on arbitrary spellings. Directed normal forms
of independently typed terms avoid that counterexample: eliminations cannot
have an introduction at their head, and type annotations synthesize. This
module connects that syntactic fact to the existing complete bidirectional
typing relation. Realizing those derivations at a sufficient executable
budget remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalChecking

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles)

def Normal {n : Nat} (term : Tm Head n) : Prop :=
  ∀ target, ¬ StrongNormalization.Reduces S.R term target

include facts

theorem lambda_type {n : Nat} {Γ : Ctx Head n} {body : Tm Head (n + 1)} {type : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ (.lam body) type) :
    ∃ domain codomain, TypeEq S.R Γ type (.pi domain codomain) := by
  obtain ⟨domain, codomain, level, functionFormed, universeWitness, _, below⟩ := typed.generation
  obtain ⟨domain', codomain', equal, _, _⟩ := Below.pi_source facts
    (TypeLe.toBelow below (Typed.isType typed formed)) formed
    (IsType.refl ⟨level, universeWitness, functionFormed⟩)
  exact ⟨domain', codomain', equal⟩

theorem pair_type {n : Nat} {Γ : Ctx Head n} {first second type : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ (.pair first second) type) :
    ∃ domain codomain, TypeEq S.R Γ type (.sigma domain codomain) := by
  obtain ⟨domain, codomain, level, pairFormed, universeWitness, _, _, below⟩ := typed.generation
  obtain ⟨domain', codomain', equal, _, _⟩ := Below.sigma_source facts
    (TypeLe.toBelow below (Typed.isType typed formed)) formed
    (IsType.refl ⟨level, universeWitness, pairFormed⟩)
  exact ⟨domain', codomain', equal⟩

theorem refl_type {n : Nat} {Γ : Ctx Head n} {subject type : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ (.refl subject) type) :
    ∃ carrier, TypeEq S.R Γ type (.id carrier subject subject) := by
  obtain ⟨carrier, _, below⟩ := typed.generation
  exact ⟨carrier, (TypeLe.id_eq facts below (Typed.isType typed formed) formed).symm⟩

theorem type_synthesizes {n : Nat} {Γ : Ctx Head n} {term : Tm Head n}
    (formed : CtxFormed S.R Γ) (type : IsType S.R Γ term)
    (checkable : Bidirectional .check term) : Bidirectional .synth term := by
  obtain ⟨level, _, typed⟩ := type
  cases checkable with
  | lam _ =>
      obtain ⟨domain, codomain, same⟩ := lambda_type facts formed typed
      exact False.elim (TypeEq.pi_ne_head facts formed same.symm)
  | pair _ _ =>
      obtain ⟨domain, codomain, same⟩ := pair_type facts formed typed
      exact False.elim (TypeEq.sigma_ne_head facts formed same.symm)
  | refl _ =>
      obtain ⟨carrier, same⟩ := refl_type facts formed typed
      exact False.elim (TypeEq.id_ne_head facts formed same.symm)
  | synthesized synthesizes => exact synthesizes

theorem function_synthesizes {n : Nat} {Γ : Ctx Head n} {function domain : Tm Head n}
    {codomain : Tm Head (n + 1)} (formed : CtxFormed S.R Γ)
    (typed : Typed S.R Γ function (.pi domain codomain))
    (notLambda : ∀ body, function ≠ .lam body)
    (checkable : Bidirectional .check function) : Bidirectional .synth function := by
  cases checkable with
  | lam _ => exact False.elim (notLambda _ rfl)
  | pair _ _ =>
      obtain ⟨domain', codomain', same⟩ := pair_type facts formed typed
      exact False.elim (TypeEq.pi_ne_sigma facts formed same)
  | refl _ =>
      obtain ⟨carrier, same⟩ := refl_type facts formed typed
      exact False.elim (TypeEq.pi_ne_id facts formed same)
  | synthesized synthesizes => exact synthesizes

theorem pair_synthesizes {n : Nat} {Γ : Ctx Head n} {value domain : Tm Head n}
    {codomain : Tm Head (n + 1)} (formed : CtxFormed S.R Γ)
    (typed : Typed S.R Γ value (.sigma domain codomain))
    (notPair : ∀ first second, value ≠ .pair first second)
    (checkable : Bidirectional .check value) : Bidirectional .synth value := by
  cases checkable with
  | lam _ =>
      obtain ⟨domain', codomain', same⟩ := lambda_type facts formed typed
      exact False.elim (TypeEq.pi_ne_sigma facts formed same.symm)
  | pair _ _ => exact False.elim (notPair _ _ rfl)
  | refl _ =>
      obtain ⟨carrier, same⟩ := refl_type facts formed typed
      exact False.elim (TypeEq.sigma_ne_id facts formed same)
  | synthesized synthesizes => exact synthesizes

/-- Normalization supplies membership in the checking fragment from an
independent typing derivation; fragment membership is not an input. -/
theorem normal_checkable {n : Nat} (term : Tm Head n) :
    ∀ {Γ : Ctx Head n} {type : Tm Head n}, CtxFormed S.R Γ → Typed S.R Γ term type →
      Normal (S := S) term → Bidirectional .check term := by
  induction term with
  | var index => intros; exact .synthesized (.var index)
  | head head => intros; exact .synthesized (.head head)
  | const name => intros; exact .synthesized (.const name)
  | pi domain codomain ihDomain ihCodomain =>
      intro Γ type formed typed normal
      obtain ⟨first, second, _, domainTyped, firstUniverse, codomainTyped, secondUniverse, _, _⟩ := typed.generation
      have domainType : IsType S.R Γ domain := ⟨first, firstUniverse, domainTyped⟩
      have extended : CtxFormed S.R (.snoc Γ domain) := .snoc formed domainType
      exact .synthesized (.pi
        (type_synthesizes facts formed domainType
          (ihDomain formed domainTyped (fun _ step => normal _ (.congPiDom step))))
        (type_synthesizes facts extended ⟨second, secondUniverse, codomainTyped⟩
          (ihCodomain extended codomainTyped (fun _ step => normal _ (.congPiCod step)))))
  | sigma domain codomain ihDomain ihCodomain =>
      intro Γ type formed typed normal
      obtain ⟨first, second, _, domainTyped, firstUniverse, codomainTyped, secondUniverse, _, _⟩ := typed.generation
      have domainType : IsType S.R Γ domain := ⟨first, firstUniverse, domainTyped⟩
      have extended : CtxFormed S.R (.snoc Γ domain) := .snoc formed domainType
      exact .synthesized (.sigma
        (type_synthesizes facts formed domainType
          (ihDomain formed domainTyped (fun _ step => normal _ (.congSigmaDom step))))
        (type_synthesizes facts extended ⟨second, secondUniverse, codomainTyped⟩
          (ihCodomain extended codomainTyped (fun _ step => normal _ (.congSigmaCod step)))))
  | id carrier first second ihCarrier ihFirst ihSecond =>
      intro Γ type formed typed normal
      obtain ⟨level, carrierTyped, universeWitness, firstTyped, secondTyped, _⟩ := typed.generation
      exact .synthesized (.id
        (type_synthesizes facts formed ⟨level, universeWitness, carrierTyped⟩
          (ihCarrier formed carrierTyped (fun _ step => normal _ (.congIdTy step))))
        (ihFirst formed firstTyped (fun _ step => normal _ (.congIdLeft step)))
        (ihSecond formed secondTyped (fun _ step => normal _ (.congIdRight step))))
  | lam body ih =>
      intro Γ type formed typed normal
      obtain ⟨domain, codomain, level, functionFormed, universeWitness, bodyTyped, _⟩ := typed.generation
      have domainType := (IsType.pi_parts ⟨level, universeWitness, functionFormed⟩).1
      exact .lam (ih (.snoc formed domainType) bodyTyped (fun _ step => normal _ (.congLam step)))
  | app function argument ihFunction ihArgument =>
      intro Γ type formed typed normal
      obtain ⟨domain, codomain, functionTyped, argumentTyped, _⟩ := typed.generation
      have functionCheck := ihFunction formed functionTyped (fun _ step => normal _ (.congAppFun step))
      have functionSynth := function_synthesizes facts formed functionTyped
        (fun body same => by subst function; exact normal _ (.betaPi body argument)) functionCheck
      exact .synthesized (.app functionSynth
        (ihArgument formed argumentTyped (fun _ step => normal _ (.congAppArg step))))
  | pair first second ihFirst ihSecond =>
      intro Γ type formed typed normal
      obtain ⟨_, _, _, _, _, firstTyped, secondTyped, _⟩ := typed.generation
      exact .pair (ihFirst formed firstTyped (fun _ step => normal _ (.congPairFst step)))
        (ihSecond formed secondTyped (fun _ step => normal _ (.congPairSnd step)))
  | fst value ih =>
      intro Γ type formed typed normal
      obtain ⟨_, _, valueTyped, _⟩ := typed.generation
      have valueCheck := ih formed valueTyped (fun _ step => normal _ (.congFst step))
      exact .synthesized (.fst (pair_synthesizes facts formed valueTyped
        (fun first second same => by subst value; exact normal _ (.betaSigmaFst first second)) valueCheck))
  | snd value ih =>
      intro Γ type formed typed normal
      obtain ⟨_, _, valueTyped, _⟩ := typed.generation
      have valueCheck := ih formed valueTyped (fun _ step => normal _ (.congSnd step))
      exact .synthesized (.snd (pair_synthesizes facts formed valueTyped
        (fun first second same => by subst value; exact normal _ (.betaSigmaSnd first second)) valueCheck))
  | refl value ih =>
      intro Γ type formed typed normal
      obtain ⟨_, valueTyped, _⟩ := typed.generation
      exact .refl (ih formed valueTyped (fun _ step => normal _ (.congRefl step)))

theorem normal_type_synthesizes {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : IsType S.R Γ type) (normal : Normal (S := S) type) :
    Bidirectional .synth type := by
  obtain ⟨level, universeWitness, derivation⟩ := typed
  exact type_synthesizes facts formed ⟨level, universeWitness, derivation⟩
    (normal_checkable facts type formed derivation normal)

variable (algebra : CumulativeAlgebra S.R)
variable (headTypingUnique : ∀ {head first second : Head},
  S.R.headTyping head first → S.R.headTyping head second → first = second)

include algebra headTypingUnique

theorem normal_checked {n : Nat} {Γ : Ctx Head n} {term type : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ term type) (normal : Normal (S := S) term) :
    Check S.R S.roles Γ term type :=
  Bidirectional.complete facts algebra headTypingUnique (normal_checkable facts term formed typed normal) formed typed

end ContextualDependentNormalChecking
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
