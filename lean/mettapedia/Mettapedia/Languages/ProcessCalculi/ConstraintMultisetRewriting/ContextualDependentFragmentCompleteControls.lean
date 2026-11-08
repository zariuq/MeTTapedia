import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersDeepControls

/-!
# The composite solver on every witness so far, and the next gap

The deep family is the last of the composed rounds: the Π round of R90, then solving in place, the
rigid formers, η-expansion, the occurs check, the two-argument spine decomposition and deep
decomposition. Run at budget 16 on the witnesses of R86, R90 and R94:

| Store | Outcome |
|---|---|
| R90's `idStore` | refuted |
| R90's `blockedStore` | commit |
| R90's `Π A X ≐ Π A A`, `Σ A X ≐ Σ A A` | commit |
| R86's pruning and crossed stores | commit |
| R77's non-pattern store | suspended (outside the fragment) |
| the R94 stores | as their own controls |

**The next gap.** Over `A X : U0`, `X ≐ Π A X` is in the dynamic pattern fragment: `X` occurs in the
codomain. The occurs check here reads domains only, since following a codomain needs the η-long
normal forms to commute with weakening, which is not yet proved. The composite solver leaves the store
suspended at budget 16 (`codomain_suspended`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragmentComplete.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDynamicFragment ContextualDependentDecisiveFragment
open ContextualDependentFragment ContextualDependentFragment.Controls
open ContextualDependentOccursCheck.Controls ContextualDependentRigidFormers.DeepControls

/-! ## The earlier witnesses -/

theorem id_deep_refuted : (run deepOnly idStore 2).readout = .refuted := by decide +kernel

theorem blocked_deep_solved : (run deepOnly blockedStore 2).readout = .commit := by decide +kernel

theorem pi_deep_solved : (run deepOnly piStore 2).readout = .commit := by decide +kernel

theorem sigma_deep_solved : (run deepOnly sigmaStore 2).readout = .commit := by decide +kernel

theorem flexFlex_deep_solved : (run deepOnly flexFlexStore 2).readout = .commit := by decide +kernel

theorem crossed_deep_solved : (run deepOnly crossedStore 2).readout = .commit := by decide +kernel

theorem repeated_deep_suspended : (run deepOnly repeatedStore 4).readout = .suspended := by decide +kernel

/-! ## The R94 witnesses through the composite solver -/

theorem carriers_deep_solved :
    (run deepOnly ContextualDependentRigidFormers.Controls.carriersStore 4).readout = .commit := by decide +kernel

theorem domains_deep_solved :
    (run deepOnly ContextualDependentRigidFormers.Controls.domainsStore 3).readout = .commit := by decide +kernel

theorem pair_deep_solved :
    (run deepOnly ContextualDependentRigidFormers.Controls.pairStore 3).readout = .commit := by decide +kernel

theorem domain_occurs_deep_refuted : (run deepOnly domainStore 2).readout = .refuted := by decide +kernel

theorem crossed_spine_deep_refuted :
    (run deepOnly ContextualDependentRigidFormers.SpineControls.crossedSpineStore 2).readout = .refuted := by
  decide +kernel

theorem deep_occurs_deep_refuted :
    (run deepOnly ContextualDependentInPlace.Controls.deepOccursStore 2).readout = .refuted := by decide +kernel

/-! ## The next gap: an occurrence in a codomain -/

theorem codomain_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.pi (.var 1) (.var 1))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

/-- `X ≐ Π A X` over `A X : U0`. -/
def codomainStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, checkedType _ self_checked⟩, ⟨universeAt twoTypes, checkedType _ codomain_checked⟩)]

theorem codomainStore_length : codomainStore.length = 1 := rfl

def codomainEquation : Equation (TotalTerm twoTypes) :=
  codomainStore.head (List.ne_nil_of_length_pos (by rw [codomainStore_length]; decide))

theorem codomainStore_eq : codomainStore = [codomainEquation] := rfl

/-- **`X ≐ Π A X` is in the dynamic pattern fragment.** -/
theorem codomain_in_fragment : InFragmentStore codomainStore := by
  rw [codomainStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have same : codomainEquation.2.1.code = codomainEquation.1.1.code := by decide +kernel
    rw [same]
    exact IsType.refl codomainEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The composite solver leaves it suspended** at budget 16. -/
theorem codomain_suspended : (run deepOnly codomainStore 4).readout = .suspended := by decide +kernel

/-- The occurs rule reads domains only. -/
theorem codomain_not_read :
    (ContextualDependentOccursCheck.occursSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete codomainStore).isNone = true := by
  decide +kernel

end ContextualDependentFragmentComplete.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
