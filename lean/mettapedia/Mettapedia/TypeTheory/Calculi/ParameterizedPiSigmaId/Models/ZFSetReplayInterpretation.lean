import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayGeneration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetTypeExpressionInterpretation
import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# Set interpretation assembled from structural typing replay

Interpret the existing scoped terms and their supplied finite replay trees.
Lambda domains come from the interpretation of their Pi formation subtree.
Conversion wrappers retain the source interpretation; they do not recover a
domain from equality of product sets. All term constructors are handled.

Successful assembly is not semantic soundness of an arbitrary rule package.
Typing of constants, universe closure, conversion soundness and independence
of accepted certificate choices are separate obligations. No term checker,
conversion authority or untyped-domain default is introduced here.
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
variable {Head : Type} {ConversionCode : Nat → Type}

abbrev Value (n : Nat) := Environment.{u} n → ZFSet.{u}

/-- The optional domain describes an interpreted Pi *type expression*.
It is not inferred from the underlying set and is not a function's output. -/
structure Meaning (n : Nat) where
  value : Value.{u} n
  productDomain? : Option (Value.{u} n)

def Meaning.plain {n : Nat} (value : Value.{u} n) : Meaning.{u} n := ⟨value, none⟩

noncomputable def assemble (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    {n : Nat} → Code Head ConversionCode n → Tm Head n → Tm Head n → Option (Meaning.{u} n)
  | _, .headType, .head head, _ => some (.plain (fun _ => heads head))
  | _, .var, .var index, _ => some (.plain (fun env => env index))
  | _, .const _ _, .const name, _ => some (.plain (fun _ => constants name))
  | _, .piForm u v domain body, .pi A B, _ => do
      let a ← assemble heads constants domain A (.head u)
      let b ← assemble heads constants body B (.head v)
      return ⟨fun env => tracePiSet (a.value env) (fun x => b.value (extend env x)), some a.value⟩
  | _, .sigmaForm u v domain body, .sigma A B, _ => do
      let a ← assemble heads constants domain A (.head u)
      let b ← assemble heads constants body B (.head v)
      return .plain (fun env => sigmaSet (a.value env) (fun x => b.value (extend env x)))
  | _, .lamIntro u formation body, .lam term, .pi A B => do
      let formed ← assemble heads constants formation (.pi A B) (.head u)
      let domain ← formed.productDomain?
      let b ← assemble heads constants body term B
      return .plain (fun env => traceLam (graph (domain env) (fun x => b.value (extend env x))))
  | _, .appElim A B function argument, .app f a, _ => do
      let f' ← assemble heads constants function f (.pi A B)
      let a' ← assemble heads constants argument a A
      return .plain (fun env => traceApp (f'.value env) (a'.value env))
  | _, .pairIntro _ _ first second, .pair x y, .sigma A B => do
      let x' ← assemble heads constants first x A
      let y' ← assemble heads constants second y (inst0 x B)
      return .plain (fun env => ZFSet.pair (x'.value env) (y'.value env))
  | _, .fstElim B pair, .fst p, type => do
      let p' ← assemble heads constants pair p (.sigma type B)
      return .plain (fun env => ZFSetOrderedPair.first (p'.value env))
  | _, .sndElim A B pair, .snd p, _ => do
      let p' ← assemble heads constants pair p (.sigma A B)
      return .plain (fun env => ZFSetOrderedPair.second (p'.value env))
  | _, .idForm _ _ left right, .id A x y, _ => do
      let x' ← assemble heads constants left x A
      let y' ← assemble heads constants right y A
      return .plain (fun env => truthCode (x'.value env = y'.value env))
  | _, .reflIntro _ _, .refl _, _ => some (.plain (fun _ => ∅))
  | _, .cumul u source, subject, .head _ => assemble heads constants source subject (.head u)
  | _, .convert A _ source _ _, subject, _ => assemble heads constants source subject A
  | _, _, _, _ => none

/-- Changing only conversion payloads leaves this model's value and retained
product domain unchanged. Acceptance still belongs to the selected checker. -/
theorem assemble_mapConversion {OtherCode : Nat → Type}
    (map : {n : Nat} → ConversionCode n → OtherCode n)
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) {n : Nat}
    (code : Code Head ConversionCode n) :
    ∀ subject type, assemble heads constants (code.mapConversion map) subject type =
      assemble heads constants code subject type := by
  induction code with
  | lamIntro _ _ _ _ _ | pairIntro _ _ _ _ _ _ _ =>
      intro subject type
      cases subject <;> try rfl
      cases type <;> simp_all only [Code.mapConversion, assemble]
  | cumul _ _ _ =>
      intro subject type
      cases type <;> simp_all only [Code.mapConversion, assemble]
  | convert A _ _ _ _ ih _ =>
      intro subject type
      exact ih subject A
  | _ =>
      intro subject type
      cases subject <;> simp_all only [Code.mapConversion, assemble]

/-- The principal view is the existing executable extraction, retaining the
original introduction domain even when result-type wrappers surround it. -/
theorem assemble_principalView (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {displayed : Tm Head n} {view : PrincipalView Head ConversionCode n},
      code.principalView displayed = some view → ∀ subject,
        assemble heads constants code subject displayed =
          assemble heads constants view.code subject view.type := by
  induction code with
  | cumul u source ih =>
      intro displayed view computed subject
      cases displayed <;> simp only [Code.principalView] at computed <;> try contradiction
      cases priorComputed : source.principalView (.head u) with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, Option.map_some, Option.some.injEq] at computed
          subst view
          exact ih priorComputed subject
  | convert A u source formation conversion ih _ =>
      intro displayed view computed subject
      simp only [Code.principalView] at computed
      cases priorComputed : source.principalView A with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, Option.map_some, Option.some.injEq] at computed
          subst view
          exact ih priorComputed subject
  | _ =>
      intro displayed view computed subject
      simp only [Code.principalView, Option.some.injEq] at computed
      subst view
      rfl

/-- On the previously interpreted fragment the replay route gives exactly
the structural value. This comparison does not assume replay acceptance. -/
theorem agrees_with_type_expressions (heads : Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) {n : Nat} (code : Code Head ConversionCode n) :
    ∀ (subject type : Tm Head n) (meaning : Meaning.{u} n)
      (supported : ZFSetTypeExpressionInterpretation.supported subject = true),
      assemble heads constants code subject type = some meaning →
      ∀ env, meaning.value env =
        ZFSetTypeExpressionInterpretation.interpret heads constants subject supported env := by
  induction code with
  | headType | var | const _ _ _ | reflIntro _ _ _ =>
      intro subject type meaning supported assembled env
      cases subject <;> simp only [assemble, reduceCtorEq, Option.some.injEq] at assembled
      all_goals subst meaning; rfl
  | piForm u v domain body ihA ihB | sigmaForm u v domain body ihA ihB =>
      intro subject type meaning supported assembled env
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨a, atA, b, atB, rfl⟩ := assembled
      obtain ⟨supportedA, supportedB⟩ := Bool.and_eq_true_iff.mp supported
      simp only [Meaning.plain, ZFSetTypeExpressionInterpretation.interpret]
      rw [ihA _ _ a supportedA atA]
      congr 1
      funext value
      exact ihB _ _ b supportedB atB (extend env value)
  | lamIntro _ _ _ _ _ =>
      intro subject type meaning supported assembled env
      cases subject <;> try { simp only [assemble, reduceCtorEq] at assembled }
      exact False.elim (Bool.noConfusion supported)
  | appElim A B function argument ihF ihA =>
      intro subject type meaning supported assembled env
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨f, atF, a, atA, rfl⟩ := assembled
      obtain ⟨supportedF, supportedA⟩ := Bool.and_eq_true_iff.mp supported
      simp only [Meaning.plain, ZFSetTypeExpressionInterpretation.interpret]
      rw [ihF _ _ f supportedF atF, ihA _ _ a supportedA atA]
  | pairIntro u formation first second _ ihX ihY =>
      intro subject type meaning supported assembled env
      cases subject <;> cases type <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨x, atX, y, atY, rfl⟩ := assembled
      obtain ⟨supportedX, supportedY⟩ := Bool.and_eq_true_iff.mp supported
      simp only [Meaning.plain, ZFSetTypeExpressionInterpretation.interpret]
      rw [ihX _ _ x supportedX atX, ihY _ _ y supportedY atY]
  | fstElim B pair ih =>
      intro subject type meaning supported assembled env
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      rename_i operand
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨p, atP, rfl⟩ := assembled
      have operandSupported : ZFSetTypeExpressionInterpretation.supported operand = true := by
        simpa only [ZFSetTypeExpressionInterpretation.supported] using supported
      simp only [Meaning.plain, ZFSetTypeExpressionInterpretation.interpret]
      rw [ih operand (.sigma type B) p operandSupported atP]
  | sndElim A B pair ih =>
      intro subject type meaning supported assembled env
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      rename_i operand
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨p, atP, rfl⟩ := assembled
      have operandSupported : ZFSetTypeExpressionInterpretation.supported operand = true := by
        simpa only [ZFSetTypeExpressionInterpretation.supported] using supported
      simp only [Meaning.plain, ZFSetTypeExpressionInterpretation.interpret]
      rw [ih operand (.sigma A B) p operandSupported atP]
  | idForm u formation left right _ ihX ihY =>
      intro subject type meaning supported assembled env
      cases subject <;> simp only [assemble, reduceCtorEq] at assembled
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨x, atX, y, atY, rfl⟩ := assembled
      obtain ⟨⟨_, supportedX⟩, supportedY⟩ :=
        (Bool.and_eq_true_iff.mp supported).imp_left Bool.and_eq_true_iff.mp
      simp only [Meaning.plain, ZFSetTypeExpressionInterpretation.interpret]
      rw [ihX _ _ x supportedX atX, ihY _ _ y supportedY atY]
  | cumul u source ih =>
      intro subject type meaning supported assembled env
      cases type <;> simp only [assemble, reduceCtorEq] at assembled
      exact ih subject (.head u) meaning supported assembled env
  | convert A u source formation conversion ih _ =>
      intro subject type meaning supported assembled env
      exact ih subject A meaning supported assembled env

variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Every accepted supplied tree assembles. For Pi subjects the original
domain interpretation is retained, which makes the lambda case possible.
This is coverage of the construction, not a typing-soundness theorem. -/
theorem accepted_assembles {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject type : Tm Head n},
      check R conversionCheck context subject type code = true →
      ∃ meaning, assemble heads constants code subject type = some meaning ∧
        ∀ A B, subject = .pi A B → ∃ domain, meaning.productDomain? = some domain := by
  induction code with
  | headType =>
      intro context subject type accepted
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true] at accepted
      exact ⟨_, rfl, by intros; contradiction⟩
  | var =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      exact ⟨_, rfl, by intros; contradiction⟩
  | const u formation _ =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      exact ⟨_, rfl, by intros; contradiction⟩
  | piForm u v domain body ihA ihB =>
      intro context subject type accepted
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨a, atA, _⟩ := ihA accepted.1.2
      obtain ⟨b, atB, _⟩ := ihB accepted.2
      exact ⟨_, by simp [assemble, atA, atB]; rfl,
        fun _ _ _ => ⟨a.value, rfl⟩⟩
  | sigmaForm u v domain body ihA ihB =>
      intro context subject type accepted
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨a, atA, _⟩ := ihA accepted.1.2
      obtain ⟨b, atB, _⟩ := ihB accepted.2
      exact ⟨_, by simp [assemble, atA, atB]; rfl, by intros; contradiction⟩
  | lamIntro u formation body ihFormation ihBody =>
      intro context subject type accepted
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨formed, atFormation, isPi⟩ := ihFormation accepted.1.2
      obtain ⟨domain, atDomain⟩ := isPi _ _ rfl
      obtain ⟨b, atBody, _⟩ := ihBody accepted.2
      exact ⟨_, by simp [assemble, atFormation, atDomain, atBody]; rfl,
        by intros; contradiction⟩
  | appElim A B function argument ihF ihA =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨f, atF, _⟩ := ihF accepted.1.1
      obtain ⟨a, atA, _⟩ := ihA accepted.1.2
      exact ⟨_, by simp [assemble, atF, atA]; rfl, by intros; contradiction⟩
  | pairIntro u formation first second _ ihX ihY =>
      intro context subject type accepted
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨x, atX, _⟩ := ihX accepted.1.2
      obtain ⟨y, atY, _⟩ := ihY accepted.2
      exact ⟨_, by simp [assemble, atX, atY]; rfl, by intros; contradiction⟩
  | fstElim B pair ih =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      obtain ⟨p, atP, _⟩ := ih accepted
      exact ⟨_, by simp [assemble, atP]; rfl, by intros; contradiction⟩
  | sndElim A B pair ih =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨p, atP, _⟩ := ih accepted.1
      exact ⟨_, by simp [assemble, atP]; rfl, by intros; contradiction⟩
  | idForm u formation left right _ ihX ihY =>
      intro context subject type accepted
      cases subject <;> cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      obtain ⟨x, atX, _⟩ := ihX accepted.1.1.2
      obtain ⟨y, atY, _⟩ := ihY accepted.1.2
      exact ⟨_, by simp [assemble, atX, atY]; rfl, by intros; contradiction⟩
  | reflIntro A term _ =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      exact ⟨_, rfl, by intros; contradiction⟩
  | cumul u source ih =>
      intro context subject type accepted
      cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true] at accepted
      exact ih accepted.1
  | convert A u source formation conversion ih _ =>
      intro context subject type accepted
      simp only [check, Bool.and_eq_true] at accepted
      exact ih accepted.1.1.2

#print axioms accepted_assembles
#print axioms agrees_with_type_expressions
#print axioms assemble_mapConversion
#print axioms assemble_principalView

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
