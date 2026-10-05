import Mettapedia.Languages.VibeITP.Presentation.AdmittedOSLF

/-! # An inhabited behavioral type still rejects a bad supplied witness -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.AdmittedOSLF.Controls

open ComputationalData ComputationalProofs ComputationalAdmission KernelFormation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def claim : Spec.Term := .lit [1]
private def declarations : List Declaration := [.axiom claim]
private def after : AdmissionState := { initialAdmission with axioms := [claim] }

private theorem admitted : Applies admissionProgram dataEqualityHost "vibe:admission-start"
    [encodeDeclarations declarations] (encodeAdmissionResult (some after)) := by
  apply (checked_start _ _).mpr
  exact .cons (.axiom rfl (by decide +kernel) rfl) (.nil _)

theorem admitted_axiom_has_behavioral_type :
    (gsltOSLF (proofSearchGSLT (kernelValidated after.theory after.nextFresh))).satisfies
      [jThm (encTerm after.theory.sig claim)]
      (derivableNativeType (kernelValidated after.theory after.nextFresh)).pred := by
  apply (admitted_nativeType_iff_checked admitted claim).mpr
  refine ⟨.axiom 0, ?_⟩
  apply (checked_entry_at_run ((checked_start _ _).mp admitted) _ _).mpr
  exact .axiom rfl

theorem behavioral_type_does_not_accept_a_missing_proof :
    Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness (.axiom 1), encode claim] (.sym "False") := by
  apply (checked_entry_refuses declarations (.axiom 1) claim).mpr
  rintro ⟨other, run, checked⟩
  have same := (admitRun_eq_some_iff _ _ _).mpr run
  have actual := (admitRun_eq_some_iff _ _ _).mpr ((checked_start _ _).mp admitted)
  rw [actual] at same
  cases Option.some.inj same
  have impossible := checked.eval
  change (none : Option Spec.Term) = some claim at impossible
  cases impossible

end Mettapedia.Languages.VibeITP.Presentation.AdmittedOSLF.Controls
