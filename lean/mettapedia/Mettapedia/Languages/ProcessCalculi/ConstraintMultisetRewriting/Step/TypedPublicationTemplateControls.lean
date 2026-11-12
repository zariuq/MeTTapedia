import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateControls

/-!
# Learned function application is a source publication

The existing template for f a is consumed as source data in the same schema
and realization pipeline as ascribed values. Its source frame has f : X,
so the application has no typing there at any type. Matching X with a
function type licenses the template's variable uses and the actual result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TemplateControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls
open NativeTypesOnTheStep.TemplateControls

def applicationCode : Code gapFrame := .template gapFrame gapRow gapTemplate (𝟙 gapFrame)

theorem retained_raw_code : applicationCode.raw = gapRow := rfl

def schema : Schema setting.levels Nat emptyState.frame where
  helpers := gapFiring.helpers
  takes := []
  reads := []
  outputs := [applicationCode]
  tells := gapFiring.tells
  guards := []
  queries := []

def pick : Pick schema := ⟨⟨[], [], [1]⟩, rfl⟩

theorem missing_output_identity_rejected :
    DependentProgram.validateChoice schema.erase ⟨[], [], []⟩ = none := rfl

theorem extra_output_identity_rejected :
    DependentProgram.validateChoice schema.erase ⟨[], [], [1, 2]⟩ = none := rfl

theorem compiled_is_actual_gap : schema.compile (state := emptyState) pick = gapFiring := rfl

theorem application_license : applicationCode.At gapAnswer := by
  change gapTemplate.Holds (gapAnswer ≫ 𝟙 gapFrame)
  rw [Category.comp_id]
  exact gapTemplate_holds

def application : Application setting.levels Nat emptyState :=
  ⟨schema, pick, gapTarget, gapAnswer, .principal gapAnswer_principal⟩

theorem source_admitted : schema.Admits (state := emptyState) pick := by
  apply application.basis.native_checks_iff.mp
  have existing := gap_templated
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩,
    existing.2.1, existing.2.2.1, existing.2.2.2, ?_⟩
  intro output member
  obtain rfl := List.mem_singleton.mp member
  exact application_license

theorem native_admitted : (realizationStep setting.levels Nat).Admits application :=
  (realization_admits_iff application).mpr source_admitted

abbrev published := (realizationStep setting.levels Nat).result application native_admitted

theorem published_is_source : published = application.sourceResult source_admitted :=
  realization_result application source_admitted

theorem output_type : (published.label 1).1.code = NativeTypesOnTheStep.Eta.u0 := rfl

theorem output_code : (published.label 1).2.code =
    .app (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩) := rfl

/-- This source class genuinely includes code not typed in its original
frame, while preserving the declared types of the filling variables. -/
theorem admitted_without_any_original_body_typing :
    (realizationStep setting.levels Nat).Admits application ∧
      ∀ type : TypeOver gapFrame, ¬ Typed Tower.rules gapFrame.raw applicationCode.raw.code type.code :=
  ⟨native_admitted, gap_no_frame_typing⟩

/-- A safe code view cannot repair the eta counterexample by selecting a
fortunate representative: its uniform license would type the original row. -/
theorem eta_has_no_uniform_code (code : Code NativeTypesOnTheStep.Eta.hFrame)
    (same : code.raw = NativeTypesOnTheStep.Eta.etaRow) :
    ¬ code.Uniform setting.levels [] := by
  intro licensed
  have all := code.uniform_types_every_solution setting.levels licensed
  exact NativeTypesOnTheStep.Eta.eta_gap.2
    (Eq.mp (congrArg (fun row : Make NativeTypesOnTheStep.Eta.hFrame =>
      NativeTypesOnTheStep.TypedAfterMatch setting.levels [] row) same) all)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TemplateControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TemplateControls.source_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TemplateControls.admitted_without_any_original_body_typing
