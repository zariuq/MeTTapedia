import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpointsArgumentsControls

/-!
# The firing round on concrete stores

Over `A : U0, G : U0 → U0, F : U0 → U0`, at `U0 → U0 → U0`:

* **`λ x y. F x ≐ λ x y. Π y (G x)`** is in the dynamic pattern fragment and has no solution: `y` occurs
  rigidly, as a domain, and `F x` cannot mention it. The general pattern step leaves it pending, since `G`
  heads an application of the right side, and R99's arguments solver is stuck on it. The firing solver
  refutes it with a certificate.
* **`λ x y. F x ≐ λ x y. G y`** has a solution: `y` occurs only as an argument of `G`. The firing solver
  commits on it, as the arguments solver does; the rigid rule does not read a flexible occurrence.

Over `A : U0, G : U0 → U0 → U0, F : U0 → U0`, at `U0 → U0 → U0`, **`λ x y. F x ≐ λ x y. Π A (G x y)`**
is solvable by pruning `G`'s second argument; `y` occurs only under `G`, so the firing solver does not
refute it, and it stays suspended: pruning under rigid structure is not a rule of the solver.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentDynamicFragment
open ContextualDependentIdEndpointsArguments.Controls

abbrev setting := ContextualDependentInversion.Controls.setting

/-- The firing solver of the tower controls, as a fuel-indexed family. -/
noncomputable def firingTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  firingFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The firing solver at budget 16. -/
noncomputable def firingOnly : Solver setting.levels := firingTower.solver 16

/-- A type over a context, formed by the budgeted formation of types. -/
abbrev formIn (Γ : Context setting.R) (code : Tower.Tm Γ.arity)
    (accepted : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 Γ code).isSome) : TypeOver Γ :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 Γ code).get accepted).val

/-- A term over a context at a formed type, checked by the executable checker. -/
abbrev termIn (Γ : Context setting.R) (type : TypeOver Γ) (code : Tower.Tm Γ.arity)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 Γ.raw code type.code).isSome = true) : TotalTerm Γ :=
  ⟨type, ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 Γ.raw code type.code).get accepted).down Γ.formed type.isType⟩⟩

/-- A run that ended because its round was stuck. -/
def isStuck {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)} : Outcome setting.levels original → Bool
  | .stuck _ => true
  | _ => false

/-! ## The contexts -/

abbrev typeContext := ContextualDependentInversion.Controls.typeContext

/-- `U0 → U0`, over `A`. -/
def endo : TypeOver typeContext := formIn typeContext (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  (by decide +kernel)

/-- `A : U0, G : U0 → U0`. -/
abbrev withG := extend typeContext endo

/-- `U0 → U0`, over `A, G`. -/
def endoG : TypeOver withG := formIn withG (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  (by decide +kernel)

/-- `A : U0, G : U0 → U0, F : U0 → U0`. -/
abbrev withMetas := extend withG endoG

/-- `U0 → U0 → U0`, over `A, G, F`. -/
def twoLocals : TypeOver withMetas :=
  formIn withMetas (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-! ## A rigid out-of-scope local beside a flexible spine -/

/-- `λ x y. F x ≐ λ x y. Π y (G x)`. -/
def rigidStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas twoLocals (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withMetas twoLocals (.lam (.lam (.pi (.var 0) (.app (.var 4) (.var 2))))) (by decide +kernel))]

theorem rigidStore_length : rigidStore.length = 1 := rfl

def rigidEquation : Equation (TotalTerm withMetas) :=
  rigidStore.head (List.ne_nil_of_length_pos (by rw [rigidStore_length]; decide))

theorem rigidStore_eq : rigidStore = [rigidEquation] := rfl

/-- **`λ x y. F x ≐ λ x y. Π y (G x)` is in the dynamic pattern fragment.** -/
theorem rigid_in_fragment : InFragmentStore rigidStore := by
  rw [rigidStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl rigidEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **R99's arguments solver is stuck on it**, at budget 16. -/
theorem rigid_arguments_stuck : isStuck (run argumentsOnly rigidStore 8) = true := by decide +kernel

/-- **The firing solver refutes it.** -/
theorem rigid_firing_refuted : (run firingOnly rigidStore 8).readout = .refuted := by decide +kernel

theorem rigid_unsolvable : ¬ (frames setting.levels).Solvable rigidStore :=
  drive_refuted firingOnly 8 _ rigid_firing_refuted

/-- **`λ x y. F x ≐ λ x y. Π y (G x)` is in the fragment and has no solution**, by a certified refutation. -/
theorem rigid_in_fragment_refuted : InFragmentStore rigidStore ∧ ¬ (frames setting.levels).Solvable rigidStore :=
  ⟨rigid_in_fragment, rigid_unsolvable⟩

/-- `λ x y. G x ≐ λ x y. Π y (F x)`: the same shape for the older metavariable `G`. -/
def olderStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas twoLocals (.lam (.lam (.app (.var 3) (.var 1)))) (by decide +kernel),
    termIn withMetas twoLocals (.lam (.lam (.pi (.var 0) (.app (.var 3) (.var 2))))) (by decide +kernel))]

theorem older_arguments_stuck : isStuck (run argumentsOnly olderStore 8) = true := by decide +kernel

/-- **The rule reads an older metavariable too.** -/
theorem older_firing_refuted : (run firingOnly olderStore 8).readout = .refuted := by decide +kernel

/-! ## A flexible out-of-scope local is not refuted -/

/-- `λ x y. F x ≐ λ x y. G y`. -/
def flexibleStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas twoLocals (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withMetas twoLocals (.lam (.lam (.app (.var 3) (.var 0)))) (by decide +kernel))]

/-- **The firing solver commits on it**, with the answer of the arguments solver. -/
theorem flexible_firing_committed : (run firingOnly flexibleStore 8).readout = .commit := by decide +kernel

theorem flexible_arguments_committed : (run argumentsOnly flexibleStore 8).readout = .commit := by decide +kernel

/-! ## Pruning under rigid structure is not read -/

/-- `U0 → U0 → U0`, over `A`. -/
def binary : TypeOver typeContext :=
  formIn typeContext (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-- `A : U0, G : U0 → U0 → U0`. -/
abbrev withBinary := extend typeContext binary

/-- `U0 → U0`, over `A, G`. -/
def endoBinary : TypeOver withBinary := formIn withBinary (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  (by decide +kernel)

/-- `A : U0, G : U0 → U0 → U0, F : U0 → U0`. -/
abbrev withPrunable := extend withBinary endoBinary

/-- `U0 → U0 → U0`, over `A, G, F`. -/
def twoLocalsPrunable : TypeOver withPrunable :=
  formIn withPrunable (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-- `λ x y. F x ≐ λ x y. Π A (G x y)`. -/
def prunableStore : EquationStore (TotalTerm withPrunable) :=
  [(termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable (.lam (.lam (.pi (.var 4) (.app (.app (.var 4) (.var 2)) (.var 1)))))
      (by decide +kernel))]

/-- **The firing solver is stuck on it, and does not refute it.** -/
theorem prunable_firing_stuck : isStuck (run firingOnly prunableStore 8) = true := by decide +kernel

/-! ## Regressions -/

theorem argument_firing_refuted : (run firingOnly ContextualDependentCensus.Controls.argumentStore 8).readout = .refuted := by
  decide +kernel
theorem twin_firing_committed :
    (run firingOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by decide +kernel
theorem flexibleBase_firing_suspended :
    (run firingOnly ContextualDependentCensus.Controls.flexibleBaseStore 8).readout = .suspended := by decide +kernel

end ContextualDependentPatternFiring.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
