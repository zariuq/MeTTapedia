import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOutputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationPrincipalControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionControls

/-!
# Learned typing succeeds without retyping an erased binding

The coerce output uses the equality learned by the actual match. The beta
counterexample retains its original function type and is refused at the
incompatible requested type, even though its normalized raw code checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OutputControls

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open DependentFull.Controls (setting triple xRow groundType toGround point ground arrow)
open ProgrammingOnTheStep.Refinement (coerceFiring x_not_ground)
open TypedPublicationAgreementControls (levels scope arrowType wideType wide identityReading requestedRow)

def coerceOutput : Output triple := ⟨xRow, groundType triple⟩

theorem coerce_raw_is_original : coerceOutput.raw = NativeTypesOnTheStep.Coerce.coerceRow := rfl

theorem coerce_source_license : coerceOutput.Uniform levels coerceFiring.information := by
  intro target substitution solved
  exact NativeTypesOnTheStep.ConversionControls.coerce_conversion_everywhere (op target) solved

theorem coerce_answer_license : coerceOutput.At toGround :=
  (coerceOutput.uniform_iff_at_principal levels NativeTypesOnTheStep.Coerce.toGround_principal).mp
    coerce_source_license

theorem coerce_realization_has_requested_type :
    Typed Tower.rules point.raw (coerceOutput.realize toGround coerce_answer_license).code ground :=
  (coerceOutput.realize toGround coerce_answer_license).typed

theorem coerce_realization_retains_value :
    (coerceOutput.realize toGround coerce_answer_license).code = .var 0 := rfl

theorem coerce_not_frame_typed : ¬ coerceOutput.raw.WellTyped := x_not_ground

def monomorphicOutput : Output scope :=
  ⟨⟨arrowType scope, ⟨.var 0, Derivable.var 0⟩⟩, wideType scope⟩

theorem monomorphic_raw_is_original : monomorphicOutput.raw = requestedRow := rfl

theorem ground_function_not_usable_at_universe_function {n : Nat} {Γ : Tower.Ctx n}
    (formed : CtxFormed Tower.rules Γ) : ¬ Below Tower.rules Γ arrow wide := by
  intro usable
  have types : IsType Tower.rules Γ wide :=
    ⟨.sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sort _,
      TypedPublicationAgreementControls.wide_typed _⟩
  have domains := (TypeLe.pi_parts (S := setting) TowerModel.facts
    (TypeLe.of_below usable) types formed).1
  have same := TypeEq.head_injective TowerModel.facts domains formed
  change (LevelTower.Head.legacyGround : Tower.Head) = .sort Tower.zero ∨ False at same
  rcases same with impossible | impossible
  · cases impossible
  · exact impossible

/-- Preserving the declared binding rejects the spurious extra typing. -/
theorem monomorphic_license_refused {target : Context Tower.rules}
    (substitution : target ⟶ scope) : ¬ monomorphicOutput.At substitution := by
  intro licensed
  exact ground_function_not_usable_at_universe_function target.formed licensed

theorem raw_success_does_not_license_publication :
    (monomorphicOutput.raw.reindex identityReading).WellTyped ∧
      ¬ monomorphicOutput.At identityReading :=
  ⟨TypedPublicationAgreementControls.identity_reading_types_requested_row,
    monomorphic_license_refused identityReading⟩

theorem principal_raw_success_still_refused :
    (monomorphicOutput.raw.reindex TypedPublicationPrincipalControls.answer).WellTyped ∧
      ¬ monomorphicOutput.At TypedPublicationPrincipalControls.answer :=
  ⟨TypedPublicationPrincipalControls.answer_types_raw_row,
    monomorphic_license_refused TypedPublicationPrincipalControls.answer⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OutputControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OutputControls.coerce_answer_license
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OutputControls.principal_raw_success_still_refused
