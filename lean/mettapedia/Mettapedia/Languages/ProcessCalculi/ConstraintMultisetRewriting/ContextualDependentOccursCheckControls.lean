import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursCheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersControls

/-!
# The occurs check at Π and Σ types on concrete stores

* **A rigid occurrence is refused with a certificate.** Over `A X : U0`, `X ≐ Π X A` is refuted: `X`
  occurs in the domain. So is `X ≐ Σ (Π X A) A`, along two domains. The Π solver leaves both
  suspended.
* **A flexible occurrence is not refused.** Over `A : U0, G : U0 → U0, X : U0`, `X ≐ Π (G X) A` is
  solvable, by `G := λ_. A` and `X := Π A A`; the occurs rule does not fire on it and the run never
  refutes it.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursCheck.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentFragment.Controls
open ContextualDependentRigidFormers.Controls

/-- The occurs solver of the tower controls, as a fuel-indexed family. -/
abbrev occursTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  occursFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The occurs solver at budget 16. -/
def occursOnly : Solver setting.levels := occursTower.solver 16

/-- A type of `A X : U0` at `U0`, checked by the executable checker. -/
def checkedType (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 twoTypes.raw code (.head (.sort Tower.zero))).isSome = true) :
    Term twoTypes (universeAt twoTypes) :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 twoTypes.raw code (.head (.sort Tower.zero))).get accepted).down twoTypes.formed (universeAt twoTypes).isType⟩

theorem self_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.var 0) (.head (.sort Tower.zero))).isSome = true := by
  decide +kernel

theorem domain_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.pi (.var 0) (.var 2))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

theorem nested_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.sigma (.pi (.var 0) (.var 2)) (.var 2))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

/-- `X ≐ Π X A` over `A X : U0`. -/
def domainStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, checkedType _ self_checked⟩, ⟨universeAt twoTypes, checkedType _ domain_checked⟩)]

/-- `X ≐ Σ (Π X A) A` over `A X : U0`. -/
def nestedStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, checkedType _ self_checked⟩, ⟨universeAt twoTypes, checkedType _ nested_checked⟩)]

/-- **The occurs solver refutes `X ≐ Π X A`.** -/
theorem domain_refuted : (run occursOnly domainStore 2).readout = .refuted := by decide +kernel

/-- **The refutation is certified.** -/
theorem domain_unsolvable : ¬ (frames setting.levels).Solvable domainStore :=
  drive_refuted occursOnly 2 _ domain_refuted

/-- **And `X ≐ Σ (Π X A) A`, along two domains.** -/
theorem nested_refuted : (run occursOnly nestedStore 2).readout = .refuted := by decide +kernel

theorem nested_unsolvable : ¬ (frames setting.levels).Solvable nestedStore :=
  drive_refuted occursOnly 2 _ nested_refuted

/-- The Π solver leaves both suspended. -/
theorem domain_pi_suspended : (run piOnly domainStore 4).readout = .suspended := by decide +kernel

theorem nested_pi_suspended : (run piOnly nestedStore 4).readout = .suspended := by decide +kernel

/-! ## A flexible occurrence -/

theorem family_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    ContextualDependentInversion.Controls.typeContext (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `G : U0 → U0` over `A : U0`. -/
def familyType : TypeOver ContextualDependentInversion.Controls.typeContext :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 ContextualDependentInversion.Controls.typeContext
    (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).get family_formed).val

/-- `A : U0, G : U0 → U0`. -/
abbrev withFamily := extend ContextualDependentInversion.Controls.typeContext familyType

/-- `A : U0, G : U0 → U0, X : U0`. -/
abbrev flexContext := extend withFamily (universeAt withFamily)

/-- A type of `A G X` at `U0`, checked by the executable checker. -/
def checkedFlex (code : Tower.Tm 3)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 flexContext.raw code (.head (.sort Tower.zero))).isSome = true) :
    Term flexContext (universeAt flexContext) :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 flexContext.raw code (.head (.sort Tower.zero))).get accepted).down flexContext.formed
      (universeAt flexContext).isType⟩

theorem flexSelf_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 flexContext.raw (.var 0) (.head (.sort Tower.zero))).isSome = true := by
  decide +kernel

theorem flexDomain_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 flexContext.raw (.pi (.app (.var 1) (.var 0)) (.var 3))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

/-- `X ≐ Π (G X) A`: `X` occurs under the metavariable `G`. -/
def flexibleStore : EquationStore (TotalTerm flexContext) :=
  [(⟨universeAt flexContext, checkedFlex _ flexSelf_checked⟩,
    ⟨universeAt flexContext, checkedFlex _ flexDomain_checked⟩)]

/-- **The occurs rule does not fire on a flexible occurrence.** -/
theorem flexible_not_refused :
    (occursSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete flexibleStore).isNone = true := by decide +kernel

/-- **And the occurs solver does not refute it.** -/
theorem flexible_run_not_refuted : (run occursOnly flexibleStore 4).readout ≠ .refuted := by decide +kernel

end ContextualDependentOccursCheck.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
