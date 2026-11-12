import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseGap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseFamily

/-!
# The base family on the stores at a base type that is an application

The two stores on which the Σ family is stuck (`ContextualDependentEtaDepth.BaseControls`) are read by the
decomposition at every base type and committed by the base family:

* `λ G g. g X ≐ λ G g. g A` at `Π (G : U0 → U0) (g : U0 → G A). G A`: its sides have the shape (`applied_anySpines`),
  the reading reads them (`applied_spines_read`), the base family commits (`applied_base_committed`);
* `λ g. g X ≐ λ g. g A` at `Π (g : U0 → P A). P A`, with `P` a metavariable: the base family commits
  (`flex_base_committed`).

**Negative control of the reading.** At a Σ base the reading reads nothing (`sigma_spines_none`): a Σ type is not a
base type, and that store is the Σ family's.

R119's census keeps its outcomes under the base family (`base_of_final`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.BaseControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls

/-- **The decomposition at every base type reads the sides** of the store at `G A`. -/
theorem applied_spines_read : (spinesUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    appliedEquation.1.1.code appliedEquation.1.2.code appliedEquation.2.2.code).isSome = true := by
  decide +kernel

/-- **The sides have the shape of two spines of one local at a base type as it stands.** -/
theorem applied_anySpines :
    AnySpines 0 appliedEquation.1.1.code appliedEquation.1.2.code appliedEquation.2.2.code := by
  obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp applied_spines_read
  exact (spinesUnderN_rel _ 16 [] _ _ _ found).anySpines

/-- **The base family commits on the store at `G A`.** -/
theorem applied_base_committed : (run (baseTower.solver 16) appliedStore 8).readout = .commit := by decide +kernel

/-- **The base family commits on the store at `P A`**, `P` a metavariable. -/
theorem flex_base_committed : (run (baseTower.solver 16) flexStore 8).readout = .commit := by decide +kernel

/-! ## A Σ base is not a base type -/

/-- **At a Σ base the reading reads nothing.** -/
theorem sigma_spines_none : spinesUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    SigmaControls.sigmaEquation.1.1.code SigmaControls.sigmaEquation.1.2.code
    SigmaControls.sigmaEquation.2.2.code = none := by decide +kernel

/-! ## R119's census -/

open ContextualDependentIntersectionGeneral.InPlaceControls ContextualDependentIntersectionGeneral.DeadControls in
/-- **R119's census under the base family.** -/
theorem base_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (baseTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := SigmaControls.sigma_of_final final
  refine ⟨decided, ?_⟩
  have sigmaDecided : (run (sigmaTower.solver 16) problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact base_run_of_sigma (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    sigmaDecided

end ContextualDependentEtaDepth.BaseControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
