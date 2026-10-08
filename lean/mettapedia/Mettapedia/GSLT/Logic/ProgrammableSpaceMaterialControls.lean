import Mettapedia.GSLT.Logic.ProgrammableSpaceInferenceMaterial
import Mettapedia.GSLT.Core.ProgrammableSpaceInferenceControls
import Mettapedia.GSLT.Logic.ProgrammableSpaceMaterialInstances
import Mettapedia.GSLT.Logic.ProgrammableSpaceMaterialFamilies

/-!
# Infinite material support and nonconstant execution fibres

The standing successor rule generates a genuinely infinite material support.
Every finite prefix misses a particular coded member. Arbitrarily delayed
fair executions agree eventually while disagreeing at the same finite budget.

The ordinary authored beta action supplies an actual material continuation;
the empty unrequested space supplies none. Thus this instance uses the real
dependent family of execution children, rather than a constant replacement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceMaterialControls

open Mettapedia.GSLT.Core.ProgrammableSpaceInferenceControls
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ProgrammableSpaceInferenceMaterial

abbrev naturals : ArgumentCoding Nat := ArgumentCoding.ofEncodable Nat

theorem growing_material_contains_every_natural (number : Nat) :
    naturals.reading number ∈ eventual naturals growing :=
  (eventual_membership naturals growing growing_fair number).mpr (every_nat_derivable number)

theorem every_finite_prefix_misses_a_material_member (tick : Nat) :
    naturals.reading (tick + 1) ∈ eventual naturals growing ∧
      naturals.reading (tick + 1) ∉ prefixValue naturals growing tick := by
  refine ⟨growing_material_contains_every_natural _, ?_⟩
  exact fun present => (each_prefix_has_a_new_fact tick).1
    ((fact_member_iff naturals (growing.facts tick) (tick + 1)).mp present)

theorem infinite_material_support_never_finishes (tick : Nat) :
    prefixValue naturals growing tick ≠ eventual naturals growing := by
  intro same
  have separated := every_finite_prefix_misses_a_material_member tick
  exact separated.2 (same.symm ▸ separated.1)

theorem fair_eventual_material_agrees (delay : Nat) :
    eventual naturals growing = eventual naturals (delayed delay) :=
  fair_material_policies_agree naturals growing (delayed delay) growing_fair (delayed_fair delay)

theorem no_uniform_budget_for_fair_material_readings (budget : Nat) :
    eventual naturals growing = eventual naturals (delayed (budget + 1)) ∧
      prefixValue naturals growing (budget + 1) ≠
        prefixValue naturals (delayed (budget + 1)) (budget + 1) := by
  refine ⟨fair_eventual_material_agrees _, ?_⟩
  intro same
  apply (finite_budget_does_not_determine_fair_support budget).2.2.2
  exact Set.ext ((value_eq_iff naturals _ _).mp same)

open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceInstances
open ProgrammableSpaceMaterialInstances
open ProgrammableSpaceMaterialFamilies
open PowerClassPresheafDescent.Controls

def betaContinuation := actionContinuation languages policies policyOutcomeRead coding
  (world 3) beforeState afterRewrite (.execute actual_rewrite_action)

theorem actual_beta_has_material_continuation :
    materialContinuation languages policies policyOutcomeRead coding
        (world 3) beforeState afterRewrite (.execute actual_rewrite_action) ∈
      ((continuations languages policies policyOutcomeRead coding).models
        (parameter languages policies policyOutcomeRead coding (world 4)
          (family.map (ProgrammableSpaceMaterial.extend (world 3)) beforeState))).carrier :=
  action_is_material_member languages policies policyOutcomeRead coding
    (world 3) beforeState afterRewrite (.execute actual_rewrite_action)

theorem empty_continuation_fibre_is_empty :
    ¬ Nonempty ((continuations languages policies policyOutcomeRead coding).native.obj
      (parameter languages policies policyOutcomeRead coding (world 4)
        (emptyState languages policies (world 4)))) := by
  rintro ⟨continuation⟩
  exact empty_space_has_no_continuation languages policies policyOutcomeRead coding
    (world 4) continuation

/-- A fabricated rewrite session cannot turn an arbitrary stored symbol into
an authored program. The same symbol remains legitimate inert source data. -/
theorem fabricated_rewrite_is_excluded :
    ¬ Started languages policies
      (ReachabilityControls.fabricated languages policies .rewrite (.symbol "foreign")
        (Mettapedia.GSLT.LanguageDef.ProgrammableSpaceRewrite.Lambda.scope [])
          (0 : Nat) rewriteRequest) := by
  apply (ReachabilityControls.sound_history_does_not_validate_fabrication
    languages policies .rewrite (.symbol "foreign")
    (Mettapedia.GSLT.LanguageDef.ProgrammableSpaceRewrite.Lambda.scope [])
      (0 : Nat) rewriteRequest ?_).2
  intro admitted
  change (none : Option Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) = some rewriteRequest at admitted
  cases admitted

end Mettapedia.GSLT.ProgrammableSpaceMaterialControls
