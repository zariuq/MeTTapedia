import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaIdentitySubstitution

/-!
# A computed beta-expanded identity proof in its interpreted fibre

The checked one-sided beta cast is useful as a dependent proof only if its
proof token inhabits the actual interpreted target family. For an arbitrary
computed argument, the required local premise is membership in the domain
retained by the identity lambda's Pi-formation certificate. The argument's
syntax need not be a variable or a normal form.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (traceApp traceLam traceApp_graph_beta)
open ZFSetDependentProducts (graph)

universe u
variable {Head : Type}
variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- A real target formation: the left endpoint is the application of the
retained identity lambda, and the right endpoint reuses the argument's
certificate. No conversion evidence is hidden in this formation. -/
def betaIdentityLeftFormationCode {n : Nat} (level piLevel : Head)
    (carrier : Tm Head n)
    (carrierFormation piFormation argumentCode : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n) :
    Code Head (StructuralConversionCode.Code Head decoder.Code) n :=
  .idForm level carrierFormation
    (.appElim carrier (rename wk carrier)
      (.lamIntro piLevel piFormation .var) argumentCode)
    argumentCode

omit [DecidableEq Head] [DecidableRel R.headEq]
  [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
  [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)] in
/-- The exact assembled fibre of the retained beta-expanded identity
formation. Both admission and independent-certificate comparison reuse this
one calculation. -/
theorem betaIdentityLeftFormation_assembles {n : Nat}
    (carrier argument : Tm Head n) (level piLevel : Head)
    (carrierFormation piFormation argumentCode : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (formed arg : Meaning.{u} n) (domain : Value.{u} n)
    (atPi : assemble heads constants piFormation
      (.pi carrier (rename wk carrier)) (.head piLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atArgument : assemble heads constants argumentCode argument carrier = some arg) :
    assemble heads constants
      (betaIdentityLeftFormationCode R decoder level piLevel carrier
        carrierFormation piFormation argumentCode)
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level) =
      some (Meaning.plain (fun env =>
        ZFSetTraceProofDecoding.truthCode
          (traceApp (traceLam (graph (domain env) (fun x => x))) (arg.value env) =
            arg.value env))) := by
  have atIdentity : assemble heads constants
      (.lamIntro piLevel piFormation (.var : Code Head
        (StructuralConversionCode.Code Head decoder.Code) (n + 1)))
      (.lam (.var 0)) (.pi carrier (rename wk carrier)) =
      some (Meaning.plain (fun env => traceLam (graph (domain env) (fun x => x)))) := by
    simp [assemble, atPi, atDomain, Meaning.plain,
      ZFSetTypeExpressionInterpretation.extend]
  have atApplication : assemble heads constants
      (.appElim carrier (rename wk carrier)
        (.lamIntro piLevel piFormation .var) argumentCode)
      (.app (.lam (.var 0)) argument) carrier =
      some (Meaning.plain (fun env =>
        traceApp (traceLam (graph (domain env) (fun x => x))) (arg.value env))) := by
    change (do
      let f ← assemble heads constants
        (.lamIntro piLevel piFormation .var) (.lam (.var 0))
        (.pi carrier (rename wk carrier))
      let a ← assemble heads constants argumentCode argument carrier
      some (Meaning.plain (fun env => traceApp (f.value env) (a.value env)))) = _
    rw [atIdentity, atArgument]
    rfl
  change (do
    let left ← assemble heads constants
      (.appElim carrier (rename wk carrier)
        (.lamIntro piLevel piFormation .var) argumentCode)
      (.app (.lam (.var 0)) argument) carrier
    let right ← assemble heads constants argumentCode argument carrier
    some (Meaning.plain (fun env =>
      ZFSetTraceProofDecoding.truthCode (left.value env = right.value env)))) = _
  rw [atApplication, atArgument]
  rfl

/-- The accepted converted proof denotes the reflexivity token, and the
actual retained identity formation contains that token on every environment
where the computed argument belongs to the lambda's retained domain. -/
theorem betaIdentityLeftProof_in_formed_fibre {n : Nat}
    (context : Ctx Head n) (valid : Environment.{u} n → Prop)
    (carrier argument : Tm Head n) (level piLevel : Head)
    (carrierFormation piFormation argumentCode : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (formed arg : Meaning.{u} n) (domain : Value.{u} n)
    (atPi : assemble heads constants piFormation
      (.pi carrier (rename wk carrier)) (.head piLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atArgument : assemble heads constants argumentCode argument carrier = some arg)
    (inside : ∀ env, valid env → arg.value env ∈ domain env)
    (levelUniverse : R.isUniverse level)
    (argumentChecked : check R (betaConversionCheck R decoder) context argument carrier
      argumentCode = true)
    (formationChecked : check R (betaConversionCheck R decoder) context
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level)
      (betaIdentityLeftFormationCode R decoder level piLevel carrier
        carrierFormation piFormation argumentCode) = true) :
    let formation := betaIdentityLeftFormationCode R decoder level piLevel carrier
      carrierFormation piFormation argumentCode
    let proof := betaIdentityLeftProof R decoder carrier argument level argumentCode formation
    check R (betaConversionCheck R decoder) context (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) proof = true ∧
    assemble heads constants proof (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) =
        some (Meaning.plain (fun _ => (∅ : ZFSet.{u}))) ∧
    ∃ family,
      assemble heads constants formation
        (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level) =
          some family ∧
      ∀ env, valid env → (∅ : ZFSet.{u}) ∈ family.value env := by
  dsimp only
  have checked := betaIdentityLeftProof_checked R decoder context carrier argument level
    argumentCode (betaIdentityLeftFormationCode R decoder level piLevel carrier
      carrierFormation piFormation argumentCode) levelUniverse argumentChecked formationChecked
  let family : Meaning.{u} n := Meaning.plain (fun env =>
    ZFSetTraceProofDecoding.truthCode
      (traceApp (traceLam (graph (domain env) (fun x => x))) (arg.value env) =
        arg.value env))
  have atFamily : assemble heads constants
      (betaIdentityLeftFormationCode R decoder level piLevel carrier
        carrierFormation piFormation argumentCode)
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level) =
      some family := by
    exact betaIdentityLeftFormation_assembles R decoder heads constants carrier argument
      level piLevel carrierFormation piFormation argumentCode formed arg domain
      atPi atDomain atArgument
  refine ⟨checked, rfl, family, atFamily, ?_⟩
  intro env admitted
  change (∅ : ZFSet.{u}) ∈
    ZFSetTraceProofDecoding.truthCode
      (traceApp (traceLam (graph (domain env) (fun x => x))) (arg.value env) =
        arg.value env)
  apply (ZFSetTraceProofDecoding.mem_truthCode _ _).mpr
  exact ⟨rfl, traceApp_graph_beta (fun x => x) (inside env admitted)⟩

#print axioms betaIdentityLeftFormation_assembles
#print axioms betaIdentityLeftProof_in_formed_fibre

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
