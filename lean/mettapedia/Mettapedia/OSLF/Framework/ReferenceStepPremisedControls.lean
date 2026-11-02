import Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated
import Mettapedia.OSLF.MeTTaIL.ReferenceStepDeclaredAgreement

/-!
# Controls: a declared equation with premises in the reference relation

The guarded-binder profile authors an extrusion that declares its binding dependencies and asks the provider to allow
the extruded component. Its rules are aligned and its equation is read alike by both relations, so:

- **the reference relation reads the guarded extrusion**: an allowed key extrudes (`reference_extrudes`);
- **its relation modulo the equation is the canonical one** (`reference_stepModulo_iff`), so the profile's finite
  frontier, exact for the canonical relation, is exact for the reference relation too
  (`reference_frontier_empty_iff`);
- **a revoked key blocks it**: with no key allowed, a tucked state has no step in the reference relation modulo the
  equation (`reference_blocked`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ReferenceStepPremisedControls

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
open Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated
open Mettapedia.GSLT.LanguageDef.EquationSemantics (StepModuloEquations)

/-- The profile's rules are aligned. -/
theorem profile : ReferenceProfile language :=
  show ∀ rule ∈ language.rewrites, Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned rule = true by decide +kernel

/-- Its guarded extrusion is read alike by both relations. -/
theorem readAlike : EquationsReadAlike language :=
  show ∀ equation ∈ language.equations, equationReadAlike equation = true by decide +kernel

/-- **The reference relation reads the guarded extrusion**: an allowed key extrudes. -/
theorem reference_extrudes {ambient : Nat} (allowed : List Token) (binder : Option String)
    (name : Fin (ambient + 1)) (key : Token) (admitted : key ∈ allowed) :
    AuthoredEquation (provider allowed) language (displayedPattern binder ⟨.tucked, name, key⟩)
      (State.pattern (⟨.exposed, name, key⟩ : State ambient)) :=
  (authoredEquation_iff_readAlike profile readAlike).mp (declared_named_forward allowed binder name key admitted)

/-- **The reference relation modulo the guarded extrusion is the canonical one.** -/
theorem reference_stepModulo_iff (allowed : List Token) {source target : Pattern} :
    StepModuloEquations (base allowed) language source target ↔ StepModulo (provider allowed) language source target :=
  stepModuloEquations_iff_readAlike profile readAlike

/-- **The finite frontier is exact for the reference relation**: it is empty exactly when the reference relation modulo
the equation has no step. -/
theorem reference_frontier_empty_iff {ambient : Nat} (allowed : List Token) (source : State ambient) :
    Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile.frontier allowed source = [] ↔
      ¬ ∃ target : Pattern, StepModulo (provider allowed) language source.pattern target := by
  rw [generated_frontier_empty_iff]
  exact not_congr (exists_congr fun _ => reference_stepModulo_iff allowed)

/-- **A revoked key blocks it**: with no key allowed, the tucked state has no step. -/
theorem reference_blocked :
    ¬ ∃ target : Pattern, StepModulo (provider []) language
      (State.pattern (⟨.tucked, 0, .permit⟩ : State 0)) target :=
  (reference_frontier_empty_iff [] _).mp (by decide +kernel)

end Mettapedia.OSLF.Framework.ReferenceStepPremisedControls
