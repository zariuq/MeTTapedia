import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaReduction

/-!
# Variable membership and admission at retained lambda domains

Context assembly supplies membership in the actual lookup formation. An
independently checked qualified formation of the displayed type is compared
with that certificate, while cumulative variable wrappers use monotonicity
of the interpreted universe heads. The argument can therefore move from a
lower to a genuinely larger domain without identifying those domains.

The root-beta consequence inspects the actual Pi-formation children of the
lambda certificate. It derives its local admission premise for variable
arguments; it does not assume semantic soundness for arbitrary terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (headsMonotone : ∀ u v, R.cumulative u v → heads u ⊆ heads v)

include headsMonotone

/-- A variable displayed at a universe head belongs to that interpreted head,
including a chain of cumulative wrappers. The original membership is read
from the supplied context certificate, not assumed for all checked terms. -/
theorem variable_head_membership (contextCode : ContextCode Head NoConversion n)
    (code : Code Head NoConversion n) :
    ∀ {context : Ctx Head n} {index : Fin n} {level : Head} {valid : Environment.{u} n → Prop},
      check R noConversionCheck context (.var index) (.head level) code = true →
      assembleContext heads constants contextCode context = some valid →
      ∀ env, valid env → env index ∈ heads level := by
  induction code with
  | var =>
      intro context index level valid checked atContext env admitted
      simp only [check, decide_eq_true_eq] at checked
      obtain ⟨meaning, assembled, member⟩ := lookupFormation_membership noConversionRename
        heads constants contextCode atContext index env admitted
      rw [← checked] at assembled
      have value := agrees_with_type_expressions heads constants
        (contextCode.lookupFormation noConversionRename index).2 (.head level)
        (.head (contextCode.lookupFormation noConversionRename index).1) meaning rfl assembled env
      change meaning.value env = heads level at value
      exact value ▸ member
  | cumul sourceLevel source ih =>
      intro context index level valid checked atContext env admitted
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact headsMonotone sourceLevel level checked.2 (ih contextCode checked.1 atContext env admitted)
  | convert _ _ _ _ impossible _ _ => exact nomatch impossible
  | _ => intros; simp_all only [check, Bool.false_eq_true]

/-- An actual accepted variable certificate inhabits an independently supplied
qualified formation of its displayed type. In the cumulative case only head
monotonicity is used; no equality between the source and target universes is
introduced. -/
theorem variable_membership
    (contextCode : ContextCode Head NoConversion n)
    (argumentCode formation : Code Head NoConversion n) (argument type : Meaning.{u} n)
    {context : Ctx Head n} {index : Fin n} {A : Tm Head n} {level : Head}
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (argumentChecked : check R noConversionCheck context (.var index) A argumentCode = true)
    (formationChecked : check R noConversionCheck context A (.head level) formation = true)
    (qualified : formation.neutralEliminations A (.head level) = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atArgument : assemble heads constants argumentCode (.var index) A = some argument)
    (atFormation : assemble heads constants formation A (.head level) = some type)
    (env : Environment.{u} n) (admitted : valid env) : argument.value env ∈ type.value env := by
  have argumentValue := agrees_with_type_expressions heads constants argumentCode
    (.var index) A argument rfl atArgument env
  change argument.value env = env index at argumentValue
  rw [argumentValue]
  cases argumentCode with
  | var =>
      simp only [check, decide_eq_true_eq] at argumentChecked
      subst A
      obtain ⟨lookup, atLookup, member⟩ := lookupFormation_membership noConversionRename
        heads constants contextCode atContext index env admitted
      have lookupChecked := (contextCode.lookupFormation_checked R noConversionCheck
        noConversionRename (fun _ impossible => nomatch impossible) contextChecked index).2
      have agree := assemble_neutralEliminations_coherent heads constants R formation
        formationChecked qualified atFormation lookupChecked atLookup
        (EqualOrHeads.heads level (contextCode.lookupFormation noConversionRename index).1)
      exact (congrArg (fun meaning => meaning.value env) agree.symm) ▸ member
  | cumul sourceLevel source =>
      cases A <;> simp only [check, Bool.false_eq_true] at argumentChecked
      rename_i targetLevel
      have member := variable_head_membership heads constants R headsMonotone contextCode
        (.cumul sourceLevel source) (context := context) (index := index) (level := targetLevel)
        argumentChecked atContext env admitted
      have typeValue := agrees_with_type_expressions heads constants formation
        (.head targetLevel) (.head level) type rfl atFormation env
      change type.value env = heads targetLevel at typeValue
      exact typeValue.symm ▸ member
  | convert _ _ _ _ impossible => exact nomatch impossible
  | _ => simp only [check, Bool.false_eq_true] at argumentChecked

/-- Admission at the actual retained Pi domain follows from checking a
variable argument and qualifying that extracted domain-formation tree.
The Pi body's formation need not satisfy the qualification. -/
theorem rootBeta_variable_admitted
    (contextCode : ContextCode Head NoConversion n)
    {context : Ctx Head n} (index : Fin n) (A : Tm Head n) (B body : Tm Head (n + 1))
    (level domainLevel bodyLevel : Head)
    (formation domainCode argumentCode : Code Head NoConversion n)
    (codomainCode bodyCode : Code Head NoConversion (n + 1))
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (sourceChecked : check R noConversionCheck context (.app (.lam body) (.var index))
      (inst0 (.var index) B) (.appElim A B (.lamIntro level formation bodyCode) argumentCode) = true)
    (parts : formation.piFormation = some (domainLevel, bodyLevel, domainCode, codomainCode))
    (qualified : domainCode.neutralEliminations A (.head domainLevel) = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (env : Environment.{u} n) (admitted : valid env) :
    RootBetaAdmitted heads constants (.var index) (inst0 (.var index) B) env
      (.appElim A B (.lamIntro level formation bodyCode) argumentCode) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at sourceChecked
  have formationChecked := sourceChecked.1.1.1.2
  have argumentChecked := sourceChecked.1.2
  obtain ⟨actualDomainLevel, actualBodyLevel, actualDomain, actualBody, computed,
    _, _, domainChecked, _⟩ := formation.piFormation_checked R noConversionCheck formationChecked
  rw [parts] at computed
  cases Option.some.inj computed
  obtain ⟨formed, atFormation, _⟩ :=
    accepted_assembles heads constants R noConversionCheck formation formationChecked
  obtain ⟨domain, codomain, atDomain, _, _, domainValue⟩ :=
    assemble_piFormation heads constants formation parts atFormation
  obtain ⟨argument, atArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck argumentCode argumentChecked
  refine ⟨formed, argument, domain.value, atFormation, domainValue, atArgument, ?_⟩
  exact variable_membership heads constants R headsMonotone contextCode argumentCode domainCode
    argument domain contextChecked argumentChecked domainChecked qualified atContext atArgument atDomain env admitted

#print axioms variable_head_membership
#print axioms variable_membership
#print axioms rootBeta_variable_admitted

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
