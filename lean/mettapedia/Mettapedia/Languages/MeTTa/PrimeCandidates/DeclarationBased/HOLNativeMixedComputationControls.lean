import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedPreservation

/-!
# Mixed decoder/native overlap and admitted binder computations

A decoder step in just one repeated type annotation temporarily prevents
the exact List-iota matcher. The two authored branches nevertheless have an
explicit finite join. A separate formed example places the real nonempty map
calculation beneath a HOL proof-family binder.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeMixedComputationControls

open Presentation NativeIndexedFamilies
open FormationSensitiveHOLProofFamily FormationSensitiveHOLUniformList

abbrev jointRules := FormationSensitiveHOLProofListIntegration.rules
abbrev Directed {n : Nat} (left right : Tower.Tm n) :=
  Step jointRules.headEq left right jointRules.computation
abbrev Path {n : Nat} (left right : Tower.Tm n) :=
  ConversionCoherence.StepStar jointRules left right

def encodedCarrier : Tower.Tm 4 := proof (rawImp (.var 3) (.var 2))
def decodedCarrier : Tower.Tm 4 := implicationFamily (.var 3) (.var 2)
def duplicatedSource : Tower.Tm 4 :=
  Intrinsic.eliminateApp encodedCarrier (.var 2) (.var 1) (.var 0)
    (Intrinsic.nilApp encodedCarrier)
def splitMetadata : Tower.Tm 4 :=
  Intrinsic.eliminateApp decodedCarrier (.var 2) (.var 1) (.var 0)
    (Intrinsic.nilApp encodedCarrier)
def matchedMetadata : Tower.Tm 4 :=
  Intrinsic.eliminateApp decodedCarrier (.var 2) (.var 1) (.var 0)
    (Intrinsic.nilApp decodedCarrier)

theorem carrier_decode : Directed encodedCarrier decodedCarrier :=
  .root (.declared (.implication _ _))

theorem native_first : Directed duplicatedSource (.var 1) :=
  .root (.inherited (.declared ⟨.list (.nil _ _ _ _)⟩))

theorem decode_first : Directed duplicatedSource splitMetadata :=
  .congAppFun (.congAppFun (.congAppFun (.congAppFun (.congAppArg carrier_decode))))

theorem reconcile_metadata : Directed splitMetadata matchedMetadata :=
  .congAppArg (.congAppArg carrier_decode)

theorem native_after_reconciliation : Directed matchedMetadata (.var 1) :=
  .root (.inherited (.declared ⟨.list (.nil _ _ _ _)⟩))

/-- An actual critical interaction is joined using only authored steps.
No conversion test or proof-side completion is executed. -/
theorem mixed_peak_join :
    Directed duplicatedSource (.var 1) ∧ Directed duplicatedSource splitMetadata ∧
      Path splitMetadata (.var 1) :=
  ⟨native_first, decode_first,
    .tail (.tail .refl reconcile_metadata) native_after_reconciliation⟩

/-- The split syntax is not already an exact authored iota redex. Distinct
head names alone would miss this interaction through duplicated arguments. -/
theorem split_not_root {target : Tower.Tm 4} :
    ¬ jointRules.computation.step splitMetadata target := by
  intro root
  cases root with
  | inherited native =>
      cases native with
      | inherited impossible => exact impossible.elim
      | declared evidence =>
          obtain ⟨evidence⟩ := evidence
          cases evidence with
          | list evidence => cases evidence
          | rel evidence => cases evidence
  | declared decoder => cases decoder

theorem wrong_selected_branch_not_root :
    ¬ jointRules.computation.step duplicatedSource (.var 0 : Tower.Tm 4) := by
  intro root
  cases root with
  | inherited native =>
      cases native with
      | inherited impossible => exact impossible.elim
      | declared evidence =>
          obtain ⟨evidence⟩ := evidence
          cases evidence with
          | list evidence => cases evidence
          | rel evidence => cases evidence
  | declared decoder => cases decoder

theorem pi_cannot_become_a_universe {n : Nat}
    (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) (head : Tower.Head) :
    ¬ Conv jointRules.headEq (.pi domain codomain) (.head head) jointRules.computation :=
  HOLNativeMixedConversionParallel.mixedPiConversionBoundary.headDisjoint

namespace FormedBinder

open FormationSensitive
open FormationSensitiveHOLProofListIntegration
open FormationSensitiveHOLNativeMixedDecoderPreservation
  (pi_zero)
open HOLNaturalDeductionNativeTranslation

def proposition : Tower.Tm 7 :=
  rename wk (subst Consumer.objects Consumer.assumptionCode)

theorem proposition_typed :
    FormationSensitive.Typing jointRules Consumer.jointContext proposition
      (.const `HOLUniformList.prop) := by
  have typed := NativeTyping.represented_typed Consumer.assumption_represented
    Consumer.objects_typed
  exact (proof_typed typed).weaken

def binder : Tower.Tm 7 := proof (rawImp proposition proposition)
def decodedBinder : Tower.Tm 7 := implicationFamily proposition proposition
def outputType : Tower.Tm 7 := Intrinsic.listApp Consumer.elementType
def functionType : Tower.Tm 7 := .pi binder (rename wk outputType)
def source : Tower.Tm 7 := .lam (rename wk Consumer.nativeProgram)
def target : Tower.Tm 7 := .lam (rename wk Consumer.nativeInput)

theorem binder_formed :
    FormationSensitive.Typing jointRules Consumer.jointContext binder (sortTm Tower.zero) := by
  have typed := NativeTyping.represented_typed Consumer.assumption_represented
    Consumer.objects_typed
  exact (proof_typed (FormationSensitiveHOLProofFamily.proof_formed
    (FormationSensitiveHOLProofFamily.implication_proposition typed typed))).weaken

theorem functionType_formed :
    FormationSensitive.Typing jointRules Consumer.jointContext functionType (sortTm Tower.zero) := by
  apply pi_zero binder_formed
  exact (execution_typed (FormationSensitiveNativeHOLMapExecution.listApp_typed
    (Consumer.element_formed Consumer.jointContext))).weaken

theorem source_admitted : Judgment jointRules Consumer.jointContext source functionType :=
  ⟨Consumer.joint_context_formed,
    .lamIntro functionType_formed (.sort Tower.zero) Consumer.program_typed.weaken⟩

theorem computation :
    FormationSensitiveHOLProofListIntegration.Reduces source target := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec
    (FormationSensitiveHOLProofListIntegration.reduction 7)
    (fun left right _ => FormationSensitiveHOLProofListIntegration.Reduces
      (.lam (rename wk left)) (.lam (rename wk right)))
    (fun _ => .refl _)
    (fun {_ _ _} edge _ ih => .step (.congLam (edge.renameTerms wk)) ih)
    Consumer.nativeProgram Consumer.nativeInput Consumer.native_computation

theorem binder_decode :
    Directed functionType (.pi decodedBinder (rename wk outputType)) :=
  .congPiDom (.root (.declared (.implication proposition proposition)))

/-- Native beta/iota evaluation runs beneath an admitted proof-family
binder. Both the result and the decoded binder type stay admitted by the
same general preservation theorem. -/
theorem computation_admitted :
    Judgment jointRules Consumer.jointContext target functionType ∧
      Judgment jointRules Consumer.jointContext
        (.pi decodedBinder (rename wk outputType)) (sortTm Tower.zero) :=
  ⟨FormationSensitiveHOLNativeMixedPreservation.gslt_preserves source_admitted computation,
    FormationSensitiveHOLNativeMixedPreservation.step_preserves
      ⟨Consumer.joint_context_formed, functionType_formed⟩ binder_decode⟩

end FormedBinder

#print axioms carrier_decode
#print axioms mixed_peak_join
#print axioms split_not_root
#print axioms wrong_selected_branch_not_root
#print axioms pi_cannot_become_a_universe
#print axioms FormedBinder.proposition_typed
#print axioms FormedBinder.binder_formed
#print axioms FormedBinder.source_admitted
#print axioms FormedBinder.computation
#print axioms FormedBinder.binder_decode
#print axioms FormedBinder.computation_admitted

end HOLNativeMixedComputationControls
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
