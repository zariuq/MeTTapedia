import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.TypeTheory.ContextualSchemaTelescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ContextualCwf

/-!
# Explicit typed arguments for the dependent step's helpers

The existing helper telescope is compared with relative CwF comprehension.
The comparison retains every declaration. Its universal argument property
therefore applies to the helper frames used by actual dependent firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedContextual
open ContextualSchemaTelescopes

variable {Head : Type} {rules : Rules Head}

namespace Helpers

def extension : {Γ : Context rules} → Helpers Γ → Extension (cwf rules) Γ
  | _, .nil Γ => Extension.nil (C := cwf rules) Γ
  | _, .cons type rest => Extension.cons (C := cwf rules) type rest.extension

def ofExtension : {Γ : Context rules} → Extension (cwf rules) Γ → Helpers Γ
  | _, .nil Γ => Helpers.nil Γ
  | _, .cons type rest => .cons type (ofExtension rest)

theorem ofExtension_extension : {Γ : Context rules} → (helpers : Helpers Γ) →
    ofExtension helpers.extension = helpers
  | _, .nil _ => rfl
  | _, .cons type rest => by
      change Helpers.cons type (ofExtension rest.extension) = Helpers.cons type rest
      rw [ofExtension_extension rest]

theorem extension_ofExtension : {Γ : Context rules} → (telescope : Extension (cwf rules) Γ) →
    (ofExtension telescope).extension = telescope
  | _, .nil _ => rfl
  | _, .cons type rest => by
      change Extension.cons type (ofExtension rest).extension = Extension.cons type rest
      rw [extension_ofExtension rest]

def extensionEquiv (Γ : Context rules) : Helpers Γ ≃ Extension (cwf rules) Γ where
  toFun := extension
  invFun := ofExtension
  left_inv := ofExtension_extension
  right_inv := extension_ofExtension

theorem extension_target : {Γ : Context rules} → (helpers : Helpers Γ) →
    helpers.extension.target = helpers.frame
  | _, .nil _ => rfl
  | _, .cons _ rest => extension_target rest

theorem extension_length : {Γ : Context rules} → (helpers : Helpers Γ) →
    helpers.extension.length = helpers.length
  | _, .nil _ => rfl
  | _, .cons _ rest => congrArg Nat.succ (extension_length rest)

/-- The interpretation of the old context used by the step is the one from
iterated comprehension, with only the proved target-context equality transported. -/
theorem extension_weaken : {Γ : Context rules} → (helpers : Helpers Γ) →
    helpers.extension.weaken = eqToHom helpers.extension_target ≫ helpers.weaken
  | _, .nil Γ => by
      change (𝟙 Γ : Γ ⟶ Γ) = (𝟙 Γ) ≫ (𝟙 Γ)
      simp
  | Γ, .cons type rest => by
      change rest.extension.weaken ≫ projectionHom Γ type =
        eqToHom _ ≫ (rest.weaken ≫ projectionHom Γ type)
      rw [extension_weaken rest, Category.assoc]

abbrev Arguments {Γ Δ : Context rules} (helpers : Helpers Γ) (baseMap : Δ ⟶ Γ) :=
  helpers.extension.Arguments baseMap

/-- Assemble the supplied terms into the actual helper target of the dependent step. -/
def instantiate {Γ Δ : Context rules} (helpers : Helpers Γ) (baseMap : Δ ⟶ Γ)
    (args : helpers.Arguments baseMap) : Δ ⟶ helpers.frame :=
  helpers.extension.assemble baseMap args ≫ eqToHom helpers.extension_target

theorem instantiate_weaken {Γ Δ : Context rules} (helpers : Helpers Γ)
    (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap) :
    helpers.instantiate baseMap args ≫ helpers.weaken = baseMap := by
  rw [instantiate, Category.assoc, ← helpers.extension_weaken]
  exact helpers.extension.weaken_assemble baseMap args

/-- A target-context equality acts as an isomorphism on substitutions. -/
def targetSubstitutionEquiv {Γ Δ : Context rules} (helpers : Helpers Γ) :
    (Δ ⟶ helpers.frame) ≃ (Δ ⟶ helpers.extension.target) where
  toFun σ := σ ≫ eqToHom helpers.extension_target.symm
  invFun σ := σ ≫ eqToHom helpers.extension_target
  left_inv σ := by simp
  right_inv σ := by simp

/-- Every helper substitution is precisely an old-context substitution and
an explicit dependent tuple of values for the fresh helpers. -/
def openingEquiv {Γ : Context rules} (helpers : Helpers Γ) (Δ : Context rules) :
    (Δ ⟶ helpers.frame) ≃ Σ baseMap : Δ ⟶ Γ, helpers.Arguments baseMap :=
  helpers.targetSubstitutionEquiv.trans (helpers.extension.comprehensionEquiv Δ)

theorem openingEquiv_symm {Γ Δ : Context rules} (helpers : Helpers Γ)
    (assignment : Σ baseMap : Δ ⟶ Γ, helpers.Arguments baseMap) :
    (helpers.openingEquiv Δ).symm assignment = helpers.instantiate assignment.1 assignment.2 := by
  change (helpers.extension.comprehensionEquiv Δ).symm assignment ≫
      eqToHom helpers.extension_target = _
  rw [Extension.comprehensionEquiv_symm_apply]
  rfl

theorem instantiate_opening {Γ Δ : Context rules} (helpers : Helpers Γ)
    (substitution : Δ ⟶ helpers.frame) :
    helpers.instantiate (helpers.openingEquiv Δ substitution).1
      (helpers.openingEquiv Δ substitution).2 = substitution := by
  rw [← openingEquiv_symm]
  exact (helpers.openingEquiv Δ).symm_apply_apply _

theorem opening_instantiate {Γ Δ : Context rules} (helpers : Helpers Γ)
    (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap) :
    helpers.openingEquiv Δ (helpers.instantiate baseMap args) = ⟨baseMap, args⟩ := by
  rw [← openingEquiv_symm helpers ⟨baseMap, args⟩]
  exact (helpers.openingEquiv Δ).apply_symm_apply _

theorem opening_base {Γ Δ : Context rules} (helpers : Helpers Γ)
    (substitution : Δ ⟶ helpers.frame) :
    (helpers.openingEquiv Δ substitution).1 = substitution ≫ helpers.weaken := by
  have projected := helpers.instantiate_weaken
    (helpers.openingEquiv Δ substitution).1 (helpers.openingEquiv Δ substitution).2
  rw [helpers.instantiate_opening] at projected
  exact projected.symm

/-- Substitution through a fresh opening evaluates every old value under the
supplied old-context substitution. -/
theorem instantiate_old_value {Γ Δ : Context rules} (helpers : Helpers Γ)
    (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap) (value : TotalTerm Γ) :
    (value.reindex helpers.weaken).reindex (helpers.instantiate baseMap args) =
      value.reindex baseMap := by
  rw [← ContextualDependentEta.reindex_comp, helpers.instantiate_weaken]

section Solutions

open TypedEquality TypedEquality.Normalization ContextualDependentEta

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- Old knowledge is tested in the old environment recovered by comprehension. -/
theorem instantiate_old_models {Γ Δ : Context rules} (helpers : Helpers Γ)
    (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap)
    (knowledge : EquationStore (TotalTerm Γ)) :
    (frames levels).Models (helpers.instantiate baseMap args)
        ((frames levels).applyStore helpers.weaken knowledge) ↔
      (frames levels).Models baseMap knowledge := by
  rw [Frames.models_applyStore]
  change (frames levels).Models
      (helpers.instantiate baseMap args ≫ helpers.weaken) knowledge ↔ _
  rw [helpers.instantiate_weaken]

/-- All solutions, including nonprincipal families, are represented by
explicit typed arguments. No solver decision premise is needed. -/
theorem solvable_iff_arguments {Γ : Context rules} (helpers : Helpers Γ)
    (knowledge : EquationStore (TotalTerm helpers.frame)) :
    (frames levels).Solvable knowledge ↔
      ∃ (Δ : Context rules) (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap),
        (frames levels).Models (helpers.instantiate baseMap args) knowledge := by
  constructor
  · rintro ⟨Δ, substitution, solved⟩
    refine ⟨Δ, (helpers.openingEquiv Δ substitution).1,
      (helpers.openingEquiv Δ substitution).2, ?_⟩
    rwa [helpers.instantiate_opening]
  · rintro ⟨Δ, baseMap, args, solved⟩
    exact ⟨Δ, helpers.instantiate baseMap args, solved⟩

/-- Universal guards range over exactly the same solutions after opening is
read as typed arguments. The observation may depend on every helper. -/
theorem entails_iff_arguments {Γ : Context rules} (helpers : Helpers Γ)
    (knowledge : EquationStore (TotalTerm helpers.frame))
    (observation : (Δ : Context rules) → (Δ ⟶ helpers.frame) → Prop) :
    (frames levels).Entails knowledge observation ↔
      ∀ (Δ : Context rules) (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap),
        (frames levels).Models (helpers.instantiate baseMap args) knowledge →
          observation Δ (helpers.instantiate baseMap args) := by
  constructor
  · intro holds Δ baseMap args solved
    exact holds Δ (helpers.instantiate baseMap args) solved
  · intro holds Δ substitution solved
    have models : (frames levels).Models
        (helpers.instantiate (helpers.openingEquiv Δ substitution).1
          (helpers.openingEquiv Δ substitution).2) knowledge := by
      rwa [helpers.instantiate_opening]
    have result := holds Δ (helpers.openingEquiv Δ substitution).1
      (helpers.openingEquiv Δ substitution).2 models
    rwa [helpers.instantiate_opening] at result

end Solutions

end Helpers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull
