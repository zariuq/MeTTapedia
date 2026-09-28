import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayRenaming
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation

/-!
# Valid environments for the supplied context-formation tree

Each context extension uses its actual formation certificate to interpret
the new variable's type. Lookup transports that same certificate by the
existing weakening operation. The variable-membership theorem therefore
uses the actual executable lookupFormation result, not an independently
chosen formation proof whose coherence has been assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation (Extension)

universe u
variable {Head : Type} {ConversionCode : Nat → Type}

noncomputable def assembleContext (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    {n : Nat} → ContextCode Head ConversionCode n → Ctx Head n → Option (Environment.{u} n → Prop)
  | _, .nil, .nil => some (fun _ => True)
  | _, .snoc prior level formation, .snoc context A => do
      let valid ← assembleContext heads constants prior context
      let meaning ← assemble heads constants formation A (.head level)
      return fun env => valid (env ∘ wk) ∧ env 0 ∈ meaning.value (env ∘ wk)

/-- Every variable in a valid assembled context belongs to the interpretation
of its actual lookup-formation certificate. This is the variable case of
semantic typing soundness, with all weakening performed by existing code. -/
theorem lookupFormation_membership
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ {context : Ctx Head n} {valid : Environment.{u} n → Prop},
      assembleContext heads constants code context = some valid →
      ∀ (index : Fin n) (env : Environment.{u} n), valid env →
        ∃ meaning,
          assemble heads constants (code.lookupFormation renameConversion index).2
            (context.lookup index) (.head (code.lookupFormation renameConversion index).1) = some meaning ∧
          env index ∈ meaning.value env := by
  induction code with
  | nil => intro context valid assembled index; exact Fin.elim0 index
  | snoc prior level formation ih =>
      intro context valid assembled index env holds
      cases context with
      | snoc context A =>
          simp only [assembleContext, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at assembled
          obtain ⟨priorValid, atPrior, a, atA, rfl⟩ := assembled
          refine Fin.cases ?_ (fun priorIndex => ?_) index
          · refine ⟨a.reindex wk, ?_, holds.2⟩
            simpa only [ContextCode.lookupFormation, Fin.cases_zero, Ctx.lookup, rename] using
              assemble_rename renameConversion heads constants formation A (.head level) a atA wk
          · obtain ⟨meaning, atMeaning, member⟩ := ih atPrior priorIndex (env ∘ wk) holds.1
            refine ⟨meaning.reindex wk, ?_, member⟩
            simpa only [ContextCode.lookupFormation, Fin.cases_succ, Ctx.lookup, rename] using
              assemble_rename renameConversion heads constants
                (prior.lookupFormation renameConversion priorIndex).2
                (context.lookup priorIndex) (.head (prior.lookupFormation renameConversion priorIndex).1)
                meaning atMeaning wk

variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- A valid extended environment is exactly a valid prior environment and
an element of its interpreted family, using the existing set-coded CwF's
comprehension object. -/
def extensionEquiv {n : Nat} (valid : Environment.{u} n → Prop) (meaning : Meaning.{u} n) :
    { env : Environment.{u} (n + 1) // valid (env ∘ wk) ∧ env 0 ∈ meaning.value (env ∘ wk) } ≃
      Extension (fun env : { env // valid env } => meaning.value env.1) where
  toFun point := ⟨⟨point.1 ∘ wk, point.2.1⟩, ⟨point.1 0, point.2.2⟩⟩
  invFun point := ⟨extend point.1.1 point.2.1, point.1.2, point.2.2⟩
  left_inv point := by
    apply Subtype.ext
    funext index
    exact Fin.cases rfl (fun _ => rfl) index
  right_inv point := by cases point; rfl

noncomputable def comprehensionEquiv {n : Nat} (context : Ctx Head n) (A : Tm Head n)
    (code : ContextCode Head ConversionCode n) (level : Head) (formation : Code Head ConversionCode n)
    (valid : Environment.{u} n → Prop) (meaning : Meaning.{u} n)
    (extendedValid : Environment.{u} (n + 1) → Prop)
    (atContext : assembleContext heads constants code context = some valid)
    (atType : assemble heads constants formation A (.head level) = some meaning)
    (atExtension : assembleContext heads constants (.snoc code level formation)
      (.snoc context A) = some extendedValid) :
    { env // extendedValid env } ≃ Extension (fun env : { env // valid env } => meaning.value env.1) := by
  simp [assembleContext, atContext, atType] at atExtension
  subst extendedValid
  exact extensionEquiv valid meaning

theorem comprehensionEquiv_weakening {n : Nat} (context : Ctx Head n) (A : Tm Head n)
    (code : ContextCode Head ConversionCode n) (level : Head) (formation : Code Head ConversionCode n)
    (valid : Environment.{u} n → Prop) (meaning : Meaning.{u} n)
    (extendedValid : Environment.{u} (n + 1) → Prop)
    (atContext : assembleContext heads constants code context = some valid)
    (atType : assemble heads constants formation A (.head level) = some meaning)
    (atExtension : assembleContext heads constants (.snoc code level formation)
      (.snoc context A) = some extendedValid) (point : { env // extendedValid env }) :
    (comprehensionEquiv heads constants context A code level formation valid meaning extendedValid
      atContext atType atExtension point).1.1 = point.1 ∘ wk := by
  simp [assembleContext, atContext, atType] at atExtension
  subst extendedValid
  rfl

theorem comprehensionEquiv_variable {n : Nat} (context : Ctx Head n) (A : Tm Head n)
    (code : ContextCode Head ConversionCode n) (level : Head) (formation : Code Head ConversionCode n)
    (valid : Environment.{u} n → Prop) (meaning : Meaning.{u} n)
    (extendedValid : Environment.{u} (n + 1) → Prop)
    (atContext : assembleContext heads constants code context = some valid)
    (atType : assemble heads constants formation A (.head level) = some meaning)
    (atExtension : assembleContext heads constants (.snoc code level formation)
      (.snoc context A) = some extendedValid) (point : { env // extendedValid env }) :
    (comprehensionEquiv heads constants context A code level formation valid meaning extendedValid
      atContext atType atExtension point).2.1 = point.1 0 := by
  simp [assembleContext, atContext, atType] at atExtension
  subst extendedValid
  rfl

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Assembly covers every accepted supplied context tree. This asserts
existence of the environment predicate, not that every context is inhabited. -/
theorem accepted_context_assembles {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ {context : Ctx Head n}, checkContext R conversionCheck context code = true →
      ∃ valid, assembleContext heads constants code context = some valid := by
  induction code with
  | nil => intro context accepted; cases context; exact ⟨_, rfl⟩
  | snoc prior level formation ih =>
      intro context accepted
      cases context with
      | snoc context A =>
          simp only [checkContext, Bool.and_eq_true] at accepted
          obtain ⟨valid, atPrior⟩ := ih accepted.1.1
          obtain ⟨meaning, atMeaning, _⟩ :=
            accepted_assembles heads constants R conversionCheck formation accepted.2
          exact ⟨_, by simp [assembleContext, atPrior, atMeaning]; rfl⟩

#print axioms lookupFormation_membership
#print axioms accepted_context_assembles
#print axioms extensionEquiv
#print axioms comprehensionEquiv
#print axioms comprehensionEquiv_weakening
#print axioms comprehensionEquiv_variable

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
