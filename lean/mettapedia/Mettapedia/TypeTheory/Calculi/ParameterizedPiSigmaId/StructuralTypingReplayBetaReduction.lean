import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay

/-!
# Root beta contraction of retained typing evidence

The input is a supplied certificate for a known root beta redex. Contraction
instantiates its actual body certificate with its actual argument certificate
and retains cumulative result wrappers. Every accepted no-conversion input
contracts, and the computed output checks at the original displayed type.

This transforms evidence; it does not reconstruct it from an erased term.
It covers one root beta step, not arbitrary contextual normalization or
conversion certificates. Malformed input may fail or produce rejected output;
only the accepted-input contract grants typing authority.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {n : Nat}

def Code.contractBeta (body : Tm Head (n + 1)) (argument displayed : Tm Head n) :
    Code Head NoConversion n → Option (Code Head NoConversion n)
  | .cumul level source => match displayed with
      | .head _ => (source.contractBeta body argument (.head level)).map (.cumul level)
      | _ => none
  | .appElim _ B (.lamIntro _ _ bodyCode) argumentCode =>
      some (Code.instantiate noConversionRename noConversionSubstitute
        body B argument bodyCode argumentCode)
  | _ => none

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]

/-- Acceptance supplies every premise of certificate instantiation. Thus no
accepted root beta redex in this profile is missed by the algorithm. -/
theorem Code.contractBeta_checked (code : Code Head NoConversion n) :
    ∀ {context : Ctx Head n} {body : Tm Head (n + 1)} {argument displayed : Tm Head n},
      check R noConversionCheck context (.app (.lam body) argument) displayed code = true →
      ∃ result, code.contractBeta body argument displayed = some result ∧
        check R noConversionCheck context (inst0 argument body) displayed result = true := by
  induction code with
  | cumul level source ih =>
      intro context body argument displayed accepted
      cases displayed <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [Bool.and_eq_true] at accepted
      obtain ⟨result, computed, checked⟩ := ih accepted.1
      exact ⟨.cumul level result,
        by simp only [contractBeta, computed, Option.map_some],
        by simp only [check, Bool.and_eq_true]; exact ⟨checked, accepted.2⟩⟩
  | appElim A B function argumentCode _ _ =>
      intro context body argument displayed accepted
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨functionChecked, argumentChecked⟩, rfl⟩ := accepted
      cases function with
      | convert A level source formation impossible => exact nomatch impossible
      | lamIntro level formation bodyCode =>
        simp only [check, Bool.and_eq_true] at functionChecked
        refine ⟨_, rfl, ?_⟩
        exact Code.instantiate_checked noConversionRename noConversionSubstitute
          R noConversionCheck (fun _ impossible => nomatch impossible)
          (fun _ impossible => nomatch impossible) functionChecked.2 argumentChecked
      | _ => simp only [check, Bool.false_eq_true] at functionChecked
  | convert _ _ _ _ impossible _ _ => exact nomatch impossible
  | _ => intros; simp_all only [check, Bool.false_eq_true]

/-- The concrete output receipt can be used directly, without a fresh search
for a typing tree or a choice of a semantically equivalent certificate. -/
theorem Code.contractBeta_result_checked {context : Ctx Head n}
    {body : Tm Head (n + 1)} {argument displayed : Tm Head n}
    (code result : Code Head NoConversion n)
    (accepted : check R noConversionCheck context (.app (.lam body) argument) displayed code = true)
    (computed : code.contractBeta body argument displayed = some result) :
    check R noConversionCheck context (inst0 argument body) displayed result = true := by
  obtain ⟨actual, atActual, checked⟩ := code.contractBeta_checked R accepted
  rw [computed] at atActual
  cases Option.some.inj atActual
  exact checked

/-- Contraction preserves the whole formed-context judgment, and the raw
operational step is the existing beta constructor of the same calculus. -/
theorem Code.contractBeta_judgment {context : Ctx Head n}
    {body : Tm Head (n + 1)} {argument displayed : Tm Head n}
    (contextCode : ContextCode Head NoConversion n) (code : Code Head NoConversion n)
    (accepted : checkJudgment R noConversionCheck context (.app (.lam body) argument)
      displayed contextCode code = true) :
    ∃ result, code.contractBeta body argument displayed = some result ∧
      checkJudgment R noConversionCheck context (inst0 argument body)
        displayed contextCode result = true ∧
      StepCore R.computation R.headEq (.app (.lam body) argument) (inst0 argument body) := by
  simp only [checkJudgment, Bool.and_eq_true] at accepted
  obtain ⟨result, computed, checked⟩ := code.contractBeta_checked R accepted.2
  refine ⟨result, computed, ?_, .betaPi body argument⟩
  simpa only [checkJudgment, Bool.and_eq_true] using And.intro accepted.1 checked

#print axioms Code.contractBeta_checked
#print axioms Code.contractBeta_result_checked
#print axioms Code.contractBeta_judgment

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
