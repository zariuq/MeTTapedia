import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSubtermControls

/-!
# The occurs check on concrete stores

The metavariable is `F : (A : U0) (c : A → A) (x : A) → A`. Under rigid `A : U0, c : A → A, x : A`:

* `F A c x ≐ c (F A c x)` has no solution in any future context, by the occurs check at the
  rigid local type `A`. The executable check recognizes it, and the full solver refutes the store.
  The worklist round alone does not refute it: it is suspended there.
* `F A c x ≐ c x` is not an occurrence; the full solver solves it with a principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternSolver.OccursControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls ContextualDependentWorklist
open ContextualDependentPatternSolver.Controls

abbrev universeType := ContextualDependentInversion.Controls.universeType

/-- `F : (A : U0) (c : A → A) (x : A) → A`. -/
def selfWhole : TypeOver (empty Tower.rules) :=
  ⟨.pi universeType.code ContextualDependentPrune.SubtermControls.olderWhole.code,
    .sort (.max (.succ Tower.zero) (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero))), .sort _,
    .piForm universeType.formed universeType.universeWitness ContextualDependentPrune.SubtermControls.olderWhole.formed
      ContextualDependentPrune.SubtermControls.olderWhole.universeWitness (.sorts _ _)⟩

def selfSpine : Spine selfWhole :=
  .bind ⟨universeType, ContextualDependentPrune.SubtermControls.olderWhole, selfWhole, rfl⟩
    ContextualDependentPrune.SubtermControls.olderSpine

/-- The local telescope `A : U0, c : A → A, x : A` over `F`. -/
abbrev selfScope := lifted selfSpine

/-- `F A c x`. -/
def selfPattern : Pattern selfSpine selfScope where
  args := fun position => position
  injective := fun _ _ same => same
  compatible := by unfold CtxRen; decide +kernel

theorem self_application_code :
    selfPattern.application.code = (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0) : Tower.Tm 4) := by rfl'

/-- `c (F A c x)`. -/
def occurring : Term selfScope.target ((lifted selfSpine).result.reindex selfPattern.map.hom) :=
  ⟨(.app (.var 1) selfPattern.application.code : Tower.Tm 4),
    .appElim (A := (.var 2 : Tower.Tm 4)) (B := (.var 3 : Tower.Tm 5)) (.var (1 : Fin 4)) selfPattern.application.typed⟩

/-- `c x`. -/
def applied : Term selfScope.target ((lifted selfSpine).result.reindex selfPattern.map.hom) :=
  ⟨(.app (.var 1) (.var 0) : Tower.Tm 4),
    .appElim (A := (.var 2 : Tower.Tm 4)) (B := (.var 3 : Tower.Tm 5)) (.var (1 : Fin 4)) (.var (0 : Fin 4))⟩

/-- **The occurs check**: `F A c x ≐ c (F A c x)` has no solution in any future context. -/
theorem occurs_no_solution {Δ : Context Tower.rules} (solution : Δ ⟶ extend (empty Tower.rules) selfWhole) :
    ¬ (selfPattern.constraint occurring).Holds solution :=
  occurs_refuted (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    DispatchControls.tower_normalizes selfPattern (.inr (.inl ())) (.inl ())
    ⟨_, selfPattern.application, occurring⟩ rfl (by rfl') (by rfl') (by rfl') (by rfl') solution

/-- In particular there is no closed solution. -/
theorem occurs_no_closed_solution :
    ¬ ∃ solution : empty Tower.rules ⟶ extend (empty Tower.rules) selfWhole,
      (selfPattern.constraint occurring).Holds solution :=
  fun ⟨solution, held⟩ => occurs_no_solution solution held

/-- The executable check recognizes the occurrence. -/
theorem occurs_detected :
    (occursCheck (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      DispatchControls.tower_normalizes selfPattern occurring).isSome = true := by decide +kernel

/-- It does not fire on `c x`, which is not an occurrence. -/
theorem applied_not_occurrence :
    (occursCheck (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      DispatchControls.tower_normalizes selfPattern applied).isSome = false := by decide +kernel

def occursStore := closeStore (selfPattern.constraint occurring)

def appliedStore := closeStore (selfPattern.constraint applied)

/-- **The full solver refutes** the occurring store, with a certified refutation. -/
theorem occurs_store_refuted : (run full occursStore 1).readout = .refuted := by decide +kernel

theorem occurs_store_unsolvable : ¬ (frames setting.levels).Solvable occursStore :=
  ContextualDependentWorklist.Outcome.readout_eq_refuted occurs_store_refuted

/-- The worklist round alone only suspends it. -/
theorem occurs_worklist_suspended : (run worklistOnly occursStore 4).readout = .suspended := by decide +kernel

/-- `F A c x ≐ c x` is solved with a principal answer. -/
theorem applied_store_solved : (run full appliedStore 2).readout = .commit := by decide +kernel

end ContextualDependentPatternSolver.OccursControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
