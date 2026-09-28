import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayBetaReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayNeutralCoherence

/-!
# Meaning of executable root beta contraction

The semantic premise inspects the source certificate's actual lambda-domain
and argument assemblies. Membership in that retained domain licenses trace
beta; cumulative result wrappers do not change the premise. Contraction then
produces a checked certificate whose assembled value agrees with the source.

Agreement concerns values, not all assembly metadata: a redex returning a Pi
type can acquire retained-domain metadata when contracted. Global semantic
typing and general normalization are not assumed or established here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- The argument belongs to the formation domain actually retained by the
root lambda. This is a concrete local condition, not a semantic-soundness
assumption for the checker or a relation between arbitrary certificates. -/
def RootBetaAdmitted (argument displayed : Tm Head n) (env : Environment.{u} n) :
    Code Head NoConversion n → Prop
  | .cumul level source => match displayed with
      | .head _ => RootBetaAdmitted argument (.head level) env source
      | _ => False
  | .appElim A B (.lamIntro level formation _) argumentCode =>
      ∃ formed arg domain,
        assemble heads constants formation (.pi A B) (.head level) = some formed ∧
        formed.productDomain? = some domain ∧
        assemble heads constants argumentCode argument A = some arg ∧
        arg.value env ∈ domain env
  | _ => False

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Relate local argument typing to the lambda's actual extracted domain.
The argument is unrestricted syntax. Its membership must be established by
the caller. No restriction on how that membership is established is imposed. -/
theorem rootBeta_argument_admitted
    {context : Ctx Head n} {A argument : Tm Head n} {B body : Tm Head (n + 1)}
    {level domainLevel bodyLevel : Head}
    {formation domainCode argumentCode : Code Head NoConversion n}
    {codomainCode bodyCode : Code Head NoConversion (n + 1)}
    (sourceChecked : check R noConversionCheck context (.app (.lam body) argument)
      (inst0 argument B) (.appElim A B (.lamIntro level formation bodyCode) argumentCode) = true)
    (parts : formation.piFormation = some (domainLevel, bodyLevel, domainCode, codomainCode))
    (arg domain : Meaning.{u} n)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (atDomain : assemble heads constants domainCode A (.head domainLevel) = some domain)
    (env : Environment.{u} n) (member : arg.value env ∈ domain.value env) :
    RootBetaAdmitted heads constants argument (inst0 argument B) env
      (.appElim A B (.lamIntro level formation bodyCode) argumentCode) := by
  simp only [check, Bool.and_eq_true] at sourceChecked
  obtain ⟨formed, atFormation, _⟩ :=
    accepted_assembles heads constants R noConversionCheck formation sourceChecked.1.1.1.2
  obtain ⟨actualDomain, codomain, atActualDomain, _, _, retained⟩ :=
    assemble_piFormation heads constants formation parts atFormation
  rw [atDomain] at atActualDomain
  cases Option.some.inj atActualDomain
  exact ⟨formed, arg, domain.value, atFormation, retained, atArgument, member⟩

/-- The value of the exact computed certificate agrees with the source at
each environment where its actual argument is admitted. -/
theorem contractBeta_value (code : Code Head NoConversion n) :
    ∀ {context : Ctx Head n} {body : Tm Head (n + 1)} {argument displayed : Tm Head n}
      {resultCode : Code Head NoConversion n} (source : Meaning.{u} n),
      check R noConversionCheck context (.app (.lam body) argument) displayed code = true →
      assemble heads constants code (.app (.lam body) argument) displayed = some source →
      code.contractBeta body argument displayed = some resultCode →
      ∀ env, RootBetaAdmitted heads constants argument displayed env code →
      ∃ target, assemble heads constants resultCode (inst0 argument body) displayed = some target ∧
        source.value env = target.value env := by
  induction code with
  | cumul level code ih =>
      intro context body argument displayed resultCode source checked atSource computed env admitted
      cases displayed <;> simp only [check, Bool.false_eq_true] at checked
      simp only [Bool.and_eq_true] at checked
      simp only [Code.contractBeta] at computed
      cases atInner : code.contractBeta body argument (.head level) with
      | none => simp [atInner] at computed
      | some inner =>
          simp only [atInner, Option.map_some, Option.some.injEq] at computed
          subst resultCode
          obtain ⟨target, atTarget, equal⟩ := ih source checked.1 atSource atInner env admitted
          exact ⟨target, atTarget, equal⟩
  | appElim A B function argumentCode _ _ =>
      intro context body argument displayed resultCode source checked atSource computed env admitted
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
      obtain ⟨⟨functionChecked, argumentChecked⟩, rfl⟩ := checked
      cases function with
      | convert A level prior formation impossible => exact nomatch impossible
      | lamIntro level formation bodyCode =>
          simp only [Code.contractBeta, Option.some.injEq] at computed
          subst resultCode
          simp only [check, Bool.and_eq_true] at functionChecked
          obtain ⟨formed, arg, domain, atFormation, atDomain, atArgument, inside⟩ := admitted
          obtain ⟨bodyMeaning, atBody, _⟩ :=
            accepted_assembles heads constants R noConversionCheck bodyCode functionChecked.2
          exact application_lambda_instantiated_value heads constants noConversionRename
            noConversionSubstitute R noConversionCheck context level A B body argument
            formation argumentCode bodyCode formed arg source bodyMeaning domain
            functionChecked.2 atFormation atDomain atBody atArgument atSource env inside
      | _ => simp only [check, Bool.false_eq_true] at functionChecked
  | convert _ _ _ _ impossible _ _ => exact nomatch impossible
  | _ => intros; simp_all only [check, Bool.false_eq_true]

/-- Compare an arbitrary accepted source certificate, including cumulative
wrappers, against an independently checked neutral-elimination certificate
for its reduct. Neither certificate is chosen by the other. -/
theorem contractBeta_normal_reduct_value
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument displayed : Tm Head n}
    (code normalCode : Code Head NoConversion n) (source normal : Meaning.{u} n)
    (checked : check R noConversionCheck context (.app (.lam body) argument) displayed code = true)
    (atSource : assemble heads constants code (.app (.lam body) argument) displayed = some source)
    (normalChecked : check R noConversionCheck context (inst0 argument body) displayed normalCode = true)
    (qualified : normalCode.neutralEliminations (inst0 argument body) displayed = true)
    (atNormal : assemble heads constants normalCode (inst0 argument body) displayed = some normal)
    (env : Environment.{u} n)
    (admitted : RootBetaAdmitted heads constants argument displayed env code) :
    source.value env = normal.value env := by
  obtain ⟨resultCode, computed, resultChecked⟩ := code.contractBeta_checked R checked
  obtain ⟨target, atTarget, equal⟩ :=
    contractBeta_value heads constants R code source checked atSource computed env admitted
  have comparison := assemble_neutralEliminations_coherent heads constants R normalCode
    normalChecked qualified atNormal resultChecked atTarget (EqualOrHeads.refl _)
  exact equal.trans (congrArg (fun value => value.value env) comparison.symm)

/-- Independently accepted source trees agree whenever both root arguments
are admitted and their common reduct has an independently qualified tree.
The inputs may retain different internal domains and argument meanings. -/
theorem rootBeta_coherent_of_normal_reduct
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument displayed : Tm Head n}
    (leftCode rightCode normalCode : Code Head NoConversion n)
    (left right normal : Meaning.{u} n)
    (leftChecked : check R noConversionCheck context (.app (.lam body) argument) displayed leftCode = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) argument) displayed rightCode = true)
    (atLeft : assemble heads constants leftCode (.app (.lam body) argument) displayed = some left)
    (atRight : assemble heads constants rightCode (.app (.lam body) argument) displayed = some right)
    (normalChecked : check R noConversionCheck context (inst0 argument body) displayed normalCode = true)
    (qualified : normalCode.neutralEliminations (inst0 argument body) displayed = true)
    (atNormal : assemble heads constants normalCode (inst0 argument body) displayed = some normal)
    (env : Environment.{u} n)
    (leftAdmitted : RootBetaAdmitted heads constants argument displayed env leftCode)
    (rightAdmitted : RootBetaAdmitted heads constants argument displayed env rightCode) :
    left.value env = right.value env :=
  (contractBeta_normal_reduct_value heads constants R leftCode normalCode left normal
    leftChecked atLeft normalChecked qualified atNormal env leftAdmitted).trans
      (contractBeta_normal_reduct_value heads constants R rightCode normalCode right normal
        rightChecked atRight normalChecked qualified atNormal env rightAdmitted).symm

#print axioms contractBeta_value
#print axioms contractBeta_normal_reduct_value
#print axioms rootBeta_coherent_of_normal_reduct

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
