import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSolveControls

/-!
# Controls for the flexible-base round

Over `A X : U0`, at `(U0 → A) → A`, budget 16 and eight rounds:

| Store | Prune-and-solve solver | Flexible-base solver |
|---|---|---|
| `λ g. g X ≐ λ g. g A` (R99's `flexibleBaseStore`) | suspended | commit |
| `λ g. g (Π A A) ≐ λ g. g (Σ A A)` | suspended | refuted |

The first store is in the fragment and solvable by `X := A` (R99's `flexibleBase_in_fragment`,
`ContextualDependentCensusSolvable`). The second has the piece `Π A A ≐ Σ A A`, a clash of formers: the store has no
solution, certified by the refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpineEta.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentPruneSolve.Controls
open ContextualDependentCensus.Controls ContextualDependentFragment.Controls ContextualDependentConstantHeads.Controls

/-- The flexible-base solver of the tower controls, as a fuel-indexed family. -/
noncomputable def flexTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  flexFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The flexible-base solver at budget 16. -/
noncomputable def flexOnly : Solver setting.levels := flexTower.solver 16

/-! ## A spine at a flexible base type -/

theorem flexibleBase_pruneSolve_suspended :
    (run pruneSolveOnly flexibleBaseStore 8).readout = .suspended := by decide +kernel

/-- **The flexible-base solver commits on `λ g. g X ≐ λ g. g A`.** -/
theorem flexibleBase_committed : (run flexOnly flexibleBaseStore 8).readout = .commit := by decide +kernel

/-- A round that moves. -/
def moves {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {rank : {Γ : Context setting.R} → EquationStore (TotalTerm Γ) → Nat × Nat} :
    Round setting.levels rank problem → Bool
  | .stuck => false
  | _ => true

theorem ne_stuck_of_moves {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {rank : {Γ : Context setting.R} → EquationStore (TotalTerm Γ) → Nat × Nat}
    {round : Round setting.levels rank problem} (moving : moves round = true) : round ≠ .stuck := by
  intro stuck
  rw [stuck] at moving
  cases moving

/-- **The decomposition at a base shape fires on the store** at budget 16. -/
theorem flexibleBase_rest_moves :
    moves (flexRest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 flexibleBaseStore) = true := by
  decide +kernel

/-- **The flexible-base round is not stuck on the store**, by the general lemma. -/
theorem flexibleBase_round_not_stuck :
    flexRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 flexibleBaseStore ≠ .stuck :=
  flexRound_not_stuck_of_rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ 16 (ne_stuck_of_moves flexibleBase_rest_moves)

/-! ## A refutation through the pieces -/

/-- `λ g. g (Π A A) ≐ λ g. g (Σ A A)`. -/
def clashStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 flexibleBase (.lam (.app (.var 0) (.pi (.var 2) (.var 3)))) (by decide +kernel),
    at16 flexibleBase (.lam (.app (.var 0) (.sigma (.var 2) (.var 3)))) (by decide +kernel))]

theorem clash_pruneSolve_suspended : (run pruneSolveOnly clashStore 8).readout = .suspended := by decide +kernel

/-- **The flexible-base solver refutes it**: the piece `Π A A ≐ Σ A A` clashes. -/
theorem clash_refuted : (run flexOnly clashStore 8).readout = .refuted := by decide +kernel

theorem clash_unsolvable : ¬ (frames setting.levels).Solvable clashStore :=
  Outcome.readout_eq_refuted clash_refuted

end ContextualDependentSpineEta.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
