import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListEliminationPreservation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeIdentity
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeRelatorEliminationExamples
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionChecking
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionDevelopmentComplete

/-!
# Preservation for the actual combined native List, identity and relator rules

The five declared root cases share independently formed declarations and
declaration-spine argument recovery. Contextual preservation reuses the
formation-sensitive subject-reduction theorem. Checked forward steps refer
to the original executable finite decoder, never the proof-only completion.

The actual conversion boundaries are independently discharged by complete
development. The public qualification and checked-step crowns have no
external confluence or boundary premise. They assert finite preservation,
not normalization, raw-step confluence, or a total conversion search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeRelatorQualification

open Presentation NativeIndexedFamilies

variable {n : Nat}

theorem rootPreservationOfPi (boundary : PiConversionBoundary IntrinsicRelator.rules) :
    FormationSensitive.RootPreservation IntrinsicRelator.rules := by
  intro n context source target displayed formed observed root
  cases root with
  | inherited impossible => exact impossible.elim
  | delta lookup =>
      rw [IntrinsicRelator.rawSignature_valueOf_none] at lookup
      cases lookup
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence =>
          cases evidence with
          | nil => exact FormationSensitiveNativeListElimination.nil_preserves boundary formed observed
          | cons => exact FormationSensitiveNativeListElimination.cons_preserves boundary formed observed
          | identity => exact FormationSensitiveNativeIdentity.identity_preserves boundary formed observed
      | rel evidence =>
          exact FormationSensitiveNativeRelatorElimination.iota_preserves boundary formed evidence observed

theorem step_preserves_of_boundaries (piBoundary : PiConversionBoundary IntrinsicRelator.rules)
    (sigmaBoundary : SigmaConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context source displayed)
    (step : Step IntrinsicRelator.rules.headEq source target IntrinsicRelator.rules.computation) :
    FormationSensitive.Judgment IntrinsicRelator.rules context target displayed :=
  judgment.step_preserves FormationSensitiveNativeRelatorElimination.universes
    piBoundary sigmaBoundary
    (FormationSensitive.towerHeadPreservation.includeSignature IntrinsicRelator.rawSignature)
    (rootPreservationOfPi piBoundary) step

theorem steps_preserve_of_boundaries (piBoundary : PiConversionBoundary IntrinsicRelator.rules)
    (sigmaBoundary : SigmaConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context source displayed)
    (steps : ConversionCoherence.StepStar IntrinsicRelator.rules source target) :
    FormationSensitive.Judgment IntrinsicRelator.rules context target displayed :=
  judgment.steps_preserve FormationSensitiveNativeRelatorElimination.universes
    piBoundary sigmaBoundary
    (FormationSensitive.towerHeadPreservation.includeSignature IntrinsicRelator.rawSignature)
    (rootPreservationOfPi piBoundary) steps

/-- All five installed roots preserve arbitrary refined source judgments;
the native conversion boundary is discharged, not supplied by a caller. -/
theorem rootPreservation : FormationSensitive.RootPreservation IntrinsicRelator.rules :=
  rootPreservationOfPi NativeRelatorConversionParallel.nativePiConversionBoundary

theorem step_preserves {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context source displayed)
    (step : Step IntrinsicRelator.rules.headEq source target IntrinsicRelator.rules.computation) :
    FormationSensitive.Judgment IntrinsicRelator.rules context target displayed :=
  step_preserves_of_boundaries NativeRelatorConversionParallel.nativePiConversionBoundary
    NativeRelatorConversionParallel.nativeSigmaConversionBoundary judgment step

theorem steps_preserve {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context source displayed)
    (steps : ConversionCoherence.StepStar IntrinsicRelator.rules source target) :
    FormationSensitive.Judgment IntrinsicRelator.rules context target displayed :=
  steps_preserve_of_boundaries NativeRelatorConversionParallel.nativePiConversionBoundary
    NativeRelatorConversionParallel.nativeSigmaConversionBoundary judgment steps

/-- A checked original forward step needs independent source admission.
Its target is then admitted at the same displayed type without an additional
target-typing premise. Symmetric conversion codes are not forward steps. -/
theorem checkedStep_preserves {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context source displayed)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    FormationSensitive.Judgment IntrinsicRelator.rules context target displayed :=
  step_preserves judgment (NativeRelatorConversionChecking.step_iff_checked.mpr ⟨code, checked⟩)

/-- A consumer may keep the original dependent endpoints while the proof
witness computes internally; the result-type adjustment is derived. -/
theorem checkedStep_inside_identity
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context source displayed)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    FormationSensitive.Judgment IntrinsicRelator.rules context (.refl target)
      (.id displayed source source) :=
  step_preserves ⟨judgment.context, .reflIntro judgment.typing⟩
    (.congRefl (NativeRelatorConversionChecking.step_iff_checked.mpr ⟨code, checked⟩))

/-- No finite conversion code can identify a Pi constructor with a head,
even for arbitrary open raw components of the full five-root package. -/
theorem check_pi_head_rejected (code : NativeRelatorConversionChecking.Code n)
    (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) (head : Tower.Head) :
    NativeRelatorConversionChecking.check code (.pi domain codomain) (.head head) = false := by
  cases checked : NativeRelatorConversionChecking.check code (.pi domain codomain) (.head head) with
  | false => rfl
  | true =>
      exact False.elim (NativeRelatorConversionParallel.nativePiConversionBoundary.headDisjoint
        (NativeRelatorConversionChecking.check_sound checked))

theorem check_sigma_head_rejected (code : NativeRelatorConversionChecking.Code n)
    (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) (head : Tower.Head) :
    NativeRelatorConversionChecking.check code (.sigma domain codomain) (.head head) = false := by
  cases checked : NativeRelatorConversionChecking.check code (.sigma domain codomain) (.head head) with
  | false => rfl
  | true =>
      exact False.elim (NativeRelatorConversionParallel.nativeSigmaConversionBoundary.headDisjoint
        (NativeRelatorConversionChecking.check_sound checked))

namespace Examples

open FormationSensitiveNativeRelatorElimination.Examples
open NativeRelatorConversionChecking

def nilTailsStep : StepCode 12 :=
  .root (.relCons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
    (.var 5) (.var 4) (Intrinsic.nilApp (.var 11)) (Intrinsic.nilApp (.var 10))
    (.var 1) (IntrinsicRelator.nilRelApp (.var 11) (.var 10) (.var 9)))

theorem selected_nilTails_checked : checkStep nilTailsStep nilTailsSource nilTailsTarget = true := by
  decide

theorem selected_nilTails_admitted :
    FormationSensitive.Judgment IntrinsicRelator.rules
      IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      nilTailsTarget nilTailsResult :=
  checkedStep_preserves selected_nilTails_judgments.1 selected_nilTails_checked

theorem selected_nilTails_inside_identity_admitted :
    FormationSensitive.Judgment IntrinsicRelator.rules
      IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      (.refl nilTailsTarget) (.id nilTailsResult nilTailsSource nilTailsSource) :=
  checkedStep_inside_identity selected_nilTails_judgments.1 selected_nilTails_checked

theorem changed_recursive_evidence_check_rejected :
    checkStep NativeRelatorConversionChecking.Examples.relConsStep
      IntrinsicRelator.consIotaLeft redirectedRecursiveEvidence = false := by decide

theorem reverse_conversion_is_not_the_same_forward_step :
    check (.symm (.single nilTailsStep)) nilTailsTarget nilTailsSource = true ∧
      checkStep nilTailsStep nilTailsTarget nilTailsSource = false := by decide

def unformedMethod : Tower.Tm 0 :=
  .const NativeRelatorConversionChecking.Examples.missingName

def unformedRootSource : Tower.Tm 0 :=
  IntrinsicRelator.eliminateApp unformedMethod unformedMethod unformedMethod unformedMethod
    unformedMethod unformedMethod
    (Intrinsic.nilApp unformedMethod) (Intrinsic.nilApp unformedMethod)
    (IntrinsicRelator.nilRelApp unformedMethod unformedMethod unformedMethod)

def unformedRootCode : StepCode 0 :=
  .root (.relNil unformedMethod unformedMethod unformedMethod unformedMethod
    unformedMethod unformedMethod)

/-- A finite reduction code can be valid while its source has no admitted
type. Source admission cannot be replaced by successful root checking. -/
theorem checked_step_does_not_supply_source_admission :
    checkStep unformedRootCode unformedRootSource unformedMethod = true ∧
      ¬ ∃ type : Tower.Tm 0,
        FormationSensitive.Judgment IntrinsicRelator.rules .nil unformedRootSource type := by
  have checked : checkStep unformedRootCode unformedRootSource unformedMethod = true := by decide
  refine ⟨checked, ?_⟩
  rintro ⟨type, judgment⟩
  have result := checkedStep_preserves judgment checked
  obtain ⟨declaredType, sortHead, known, _, _⟩ := result.typing.constFormation
  have absent : IntrinsicRelator.rules.constantType
      NativeRelatorConversionChecking.Examples.missingName = none := by decide
  rw [absent] at known
  cases known

end Examples

#print axioms rootPreservationOfPi
#print axioms step_preserves_of_boundaries
#print axioms steps_preserve_of_boundaries
#print axioms rootPreservation
#print axioms step_preserves
#print axioms steps_preserve
#print axioms checkedStep_preserves
#print axioms checkedStep_inside_identity
#print axioms check_pi_head_rejected
#print axioms check_sigma_head_rejected
#print axioms Examples.selected_nilTails_checked
#print axioms Examples.selected_nilTails_admitted
#print axioms Examples.selected_nilTails_inside_identity_admitted
#print axioms Examples.changed_recursive_evidence_check_rejected
#print axioms Examples.reverse_conversion_is_not_the_same_forward_step
#print axioms Examples.checked_step_does_not_supply_source_admission

end FormationSensitiveNativeRelatorQualification
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
