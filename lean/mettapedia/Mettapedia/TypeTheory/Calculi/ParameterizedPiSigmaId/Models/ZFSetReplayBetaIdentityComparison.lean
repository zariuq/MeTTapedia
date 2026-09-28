import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaIdentityAdmission

/-!
# Comparing independently checked beta-identity fibres

Two certificates for the same beta-expanded identity can retain different
function domains and different argument interpretations. Each identity fibre
is nevertheless true where its own argument belongs to its own retained
domain. The comparison uses those two local admissions; it does not assume
equality of the intermediate domains or of the argument values.
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
variable {Head : Type} {n : Nat}
variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

omit [DecidableEq Head] [DecidableRel R.headEq]
  [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
  [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)] in
/-- The value of a beta-expanded identity formation is determined by its
retained function domain and argument value. This is a statement about the
actual assembled certificate, before any beta equation is applied. -/
theorem betaIdentityLeftFormation_value
    (carrier argument : Tm Head n) (level piLevel : Head)
    (carrierFormation piFormation argumentCode : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (formed arg family : Meaning.{u} n) (domain : Value.{u} n)
    (atPi : assemble heads constants piFormation
      (.pi carrier (rename wk carrier)) (.head piLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atArgument : assemble heads constants argumentCode argument carrier = some arg)
    (atFamily : assemble heads constants
      (betaIdentityLeftFormationCode R decoder level piLevel carrier
        carrierFormation piFormation argumentCode)
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level) = some family) :
    ∀ env, family.value env =
      ZFSetTraceProofDecoding.truthCode
        (traceApp (traceLam (graph (domain env) (fun x => x))) (arg.value env) =
          arg.value env) := by
  have exact := betaIdentityLeftFormation_assembles R decoder heads constants
    carrier argument level piLevel carrierFormation piFormation argumentCode
    formed arg domain atPi atDomain atArgument
  rw [exact] at atFamily
  cases Option.some.inj atFamily
  intro env
  rfl

omit [DecidableEq Head] [DecidableRel R.headEq]
  [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
  [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)] in
/-- An independently assembled beta-identity fibre is the true identity
fibre wherever its own computed argument is admitted by its own function
domain. No comparison with another certificate is needed for this step. -/
theorem betaIdentityLeftFormation_true
    (carrier argument : Tm Head n) (level piLevel : Head)
    (carrierFormation piFormation argumentCode : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (formed arg family : Meaning.{u} n) (domain : Value.{u} n)
    (atPi : assemble heads constants piFormation
      (.pi carrier (rename wk carrier)) (.head piLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atArgument : assemble heads constants argumentCode argument carrier = some arg)
    (atFamily : assemble heads constants
      (betaIdentityLeftFormationCode R decoder level piLevel carrier
        carrierFormation piFormation argumentCode)
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level) = some family)
    (env : Environment.{u} n) (inside : arg.value env ∈ domain env) :
    family.value env = ZFSetTraceProofDecoding.truthCode True := by
  rw [betaIdentityLeftFormation_value R decoder heads constants carrier argument level piLevel
    carrierFormation piFormation argumentCode formed arg family domain atPi atDomain atArgument
    atFamily env, traceApp_graph_beta (fun x => x) inside]
  simp only [eq_self]

omit [DecidableEq Head] [DecidableRel R.headEq]
  [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
  [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)] in
/-- The domain premise is necessary: at a nonempty argument outside the
retained domain, the same assembled identity fibre is false. -/
theorem betaIdentityLeftFormation_false_outside
    (carrier argument : Tm Head n) (level piLevel : Head)
    (carrierFormation piFormation argumentCode : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (formed arg family : Meaning.{u} n) (domain : Value.{u} n)
    (atPi : assemble heads constants piFormation
      (.pi carrier (rename wk carrier)) (.head piLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atArgument : assemble heads constants argumentCode argument carrier = some arg)
    (atFamily : assemble heads constants
      (betaIdentityLeftFormationCode R decoder level piLevel carrier
        carrierFormation piFormation argumentCode)
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level) = some family)
    (env : Environment.{u} n)
    (outside : arg.value env ∉ domain env) (nonempty : arg.value env ≠ ∅) :
    family.value env = ZFSetTraceProofDecoding.truthCode False ∧
      (∅ : ZFSet.{u}) ∉ family.value env := by
  have value := betaIdentityLeftFormation_value R decoder heads constants carrier argument
    level piLevel carrierFormation piFormation argumentCode formed arg family domain
    atPi atDomain atArgument atFamily env
  rw [ZFSetTraceProducts.traceApp_graph_outside (fun x => x) outside] at value
  have falseEq : ((∅ : ZFSet.{u}) = arg.value env) = False :=
    propext (iff_false_intro (Ne.symm nonempty))
  rw [falseEq] at value
  refine ⟨value, ?_⟩
  rw [value]
  intro member
  exact (ZFSetTraceProofDecoding.mem_truthCode False ∅).mp member |>.2

/-- Two independently checked beta-expanded identity formations agree on
valid environments even if their retained Π-domains and computed argument
values differ. The local admission of each argument is indispensable. -/
theorem betaIdentityLeft_independent_fibres
    (context : Ctx Head n) (valid : Environment.{u} n → Prop)
    (carrier argument : Tm Head n)
    (leftLevel rightLevel leftPiLevel rightPiLevel : Head)
    (leftCarrier leftPi leftArgument rightCarrier rightPi rightArgument : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (leftFormed rightFormed leftArg rightArg : Meaning.{u} n)
    (leftDomain rightDomain : Value.{u} n)
    (atLeftPi : assemble heads constants leftPi
      (.pi carrier (rename wk carrier)) (.head leftPiLevel) = some leftFormed)
    (atRightPi : assemble heads constants rightPi
      (.pi carrier (rename wk carrier)) (.head rightPiLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
    (atLeftArgument : assemble heads constants leftArgument argument carrier = some leftArg)
    (atRightArgument : assemble heads constants rightArgument argument carrier = some rightArg)
    (leftInside : ∀ env, valid env → leftArg.value env ∈ leftDomain env)
    (rightInside : ∀ env, valid env → rightArg.value env ∈ rightDomain env)
    (leftUniverse : R.isUniverse leftLevel) (rightUniverse : R.isUniverse rightLevel)
    (leftArgumentChecked : check R (betaConversionCheck R decoder) context argument carrier
      leftArgument = true)
    (rightArgumentChecked : check R (betaConversionCheck R decoder) context argument carrier
      rightArgument = true)
    (leftFormationChecked : check R (betaConversionCheck R decoder) context
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head leftLevel)
      (betaIdentityLeftFormationCode R decoder leftLevel leftPiLevel carrier
        leftCarrier leftPi leftArgument) = true)
    (rightFormationChecked : check R (betaConversionCheck R decoder) context
      (.id carrier (.app (.lam (.var 0)) argument) argument) (.head rightLevel)
      (betaIdentityLeftFormationCode R decoder rightLevel rightPiLevel carrier
        rightCarrier rightPi rightArgument) = true) :
    let leftFormation := betaIdentityLeftFormationCode R decoder leftLevel leftPiLevel carrier
      leftCarrier leftPi leftArgument
    let rightFormation := betaIdentityLeftFormationCode R decoder rightLevel rightPiLevel carrier
      rightCarrier rightPi rightArgument
    let leftProof := betaIdentityLeftProof R decoder carrier argument leftLevel
      leftArgument leftFormation
    let rightProof := betaIdentityLeftProof R decoder carrier argument rightLevel
      rightArgument rightFormation
    check R (betaConversionCheck R decoder) context (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) leftProof = true ∧
    check R (betaConversionCheck R decoder) context (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) rightProof = true ∧
    ∃ leftProofMeaning rightProofMeaning leftFamily rightFamily,
      assemble heads constants leftProof (.refl argument)
        (.id carrier (.app (.lam (.var 0)) argument) argument) = some leftProofMeaning ∧
      assemble heads constants rightProof (.refl argument)
        (.id carrier (.app (.lam (.var 0)) argument) argument) = some rightProofMeaning ∧
      assemble heads constants leftFormation
        (.id carrier (.app (.lam (.var 0)) argument) argument) (.head leftLevel) = some leftFamily ∧
      assemble heads constants rightFormation
        (.id carrier (.app (.lam (.var 0)) argument) argument) (.head rightLevel) = some rightFamily ∧
      ∀ env, valid env → leftProofMeaning.value env = rightProofMeaning.value env ∧
        leftProofMeaning.value env ∈ leftFamily.value env ∧
        rightProofMeaning.value env ∈ rightFamily.value env ∧
        leftFamily.value env = rightFamily.value env := by
  dsimp only
  obtain ⟨leftChecked, atLeftProof, leftFamily, atLeftFamily, leftMember⟩ :=
    betaIdentityLeftProof_in_formed_fibre R decoder heads constants context valid
      carrier argument leftLevel leftPiLevel leftCarrier leftPi leftArgument
      leftFormed leftArg leftDomain atLeftPi atLeftDomain atLeftArgument leftInside
      leftUniverse leftArgumentChecked leftFormationChecked
  obtain ⟨rightChecked, atRightProof, rightFamily, atRightFamily, rightMember⟩ :=
    betaIdentityLeftProof_in_formed_fibre R decoder heads constants context valid
      carrier argument rightLevel rightPiLevel rightCarrier rightPi rightArgument
      rightFormed rightArg rightDomain atRightPi atRightDomain atRightArgument rightInside
      rightUniverse rightArgumentChecked rightFormationChecked
  refine ⟨leftChecked, rightChecked, Meaning.plain (fun _ => (∅ : ZFSet.{u})),
    Meaning.plain (fun _ => (∅ : ZFSet.{u})), leftFamily, rightFamily,
    atLeftProof, atRightProof, atLeftFamily, atRightFamily, ?_⟩
  intro env admitted
  have leftTrue := betaIdentityLeftFormation_true R decoder heads constants carrier argument
    leftLevel leftPiLevel leftCarrier leftPi leftArgument leftFormed leftArg leftFamily
    leftDomain atLeftPi atLeftDomain atLeftArgument atLeftFamily env (leftInside env admitted)
  have rightTrue := betaIdentityLeftFormation_true R decoder heads constants carrier argument
    rightLevel rightPiLevel rightCarrier rightPi rightArgument rightFormed rightArg rightFamily
    rightDomain atRightPi atRightDomain atRightArgument atRightFamily env (rightInside env admitted)
  exact ⟨rfl, leftMember env admitted, rightMember env admitted, leftTrue.trans rightTrue.symm⟩

#print axioms betaIdentityLeftFormation_value
#print axioms betaIdentityLeftFormation_true
#print axioms betaIdentityLeftFormation_false_outside
#print axioms betaIdentityLeft_independent_fibres

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
