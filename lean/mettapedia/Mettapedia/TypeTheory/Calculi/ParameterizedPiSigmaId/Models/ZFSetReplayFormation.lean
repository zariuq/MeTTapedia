import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayFormation

/-!
# Interpretation of extracted formation evidence

The existing finite Pi/Sigma formation extractors return the precise child
certificates used by replay interpretation. Conversion and cumulative result
wrappers do not replace those children. These are equalities for actual
extraction and assembly operations, not injectivity of product set codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProducts (tracePiSet)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

theorem assemble_piFormation (code : Code Head ConversionCode n) :
    ∀ {A : Tm Head n} {B : Tm Head (n + 1)} {type : Tm Head n}
      {meaning : Meaning.{u} n} {u v : Head} {domain : Code Head ConversionCode n}
      {body : Code Head ConversionCode (n + 1)},
      code.piFormation = some (u, v, domain, body) →
      assemble heads constants code (.pi A B) type = some meaning →
      ∃ a b, assemble heads constants domain A (.head u) = some a ∧
        assemble heads constants body B (.head v) = some b ∧
        meaning.value = (fun env => tracePiSet (a.value env) (fun x => b.value (extend env x))) ∧
        meaning.productDomain? = some a.value := by
  induction code with
  | piForm u v domain body _ _ =>
      intro A B type meaning u' v' domain' body' extracted assembled
      cases Option.some.inj extracted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨a, atA, b, atB, rfl⟩ := assembled
      exact ⟨a, b, atA, atB, rfl, rfl⟩
  | cumul level source ih =>
      intro A B type meaning u v domain body extracted assembled
      cases type <;> simp only [assemble, reduceCtorEq] at assembled
      exact ih extracted assembled
  | convert A level source formation conversion ih _ =>
      intro A' B type meaning u v domain body extracted assembled
      exact ih extracted assembled
  | _ =>
      intros A B type meaning u v domain body extracted assembled
      simp only [Code.piFormation, reduceCtorEq] at extracted

theorem assemble_sigmaFormation (code : Code Head ConversionCode n) :
    ∀ {A : Tm Head n} {B : Tm Head (n + 1)} {type : Tm Head n}
      {meaning : Meaning.{u} n} {u v : Head} {domain : Code Head ConversionCode n}
      {body : Code Head ConversionCode (n + 1)},
      code.sigmaFormation = some (u, v, domain, body) →
      assemble heads constants code (.sigma A B) type = some meaning →
      ∃ a b, assemble heads constants domain A (.head u) = some a ∧
        assemble heads constants body B (.head v) = some b ∧
        meaning.value = (fun env => sigmaSet (a.value env) (fun x => b.value (extend env x))) := by
  induction code with
  | sigmaForm u v domain body _ _ =>
      intro A B type meaning u' v' domain' body' extracted assembled
      cases Option.some.inj extracted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨a, atA, b, atB, rfl⟩ := assembled
      exact ⟨a, b, atA, atB, rfl⟩
  | cumul level source ih =>
      intro A B type meaning u v domain body extracted assembled
      cases type <;> simp only [assemble, reduceCtorEq] at assembled
      exact ih extracted assembled
  | convert A level source formation conversion ih _ =>
      intro A' B type meaning u v domain body extracted assembled
      exact ih extracted assembled
  | _ =>
      intros A B type meaning u v domain body extracted assembled
      simp only [Code.sigmaFormation, reduceCtorEq] at extracted

#print axioms assemble_piFormation
#print axioms assemble_sigmaFormation

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
