import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverageReadersHalfUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableDiscovery

/-!
# The census head on the prepared store with homogeneous twins

Most readers of the flexible round read `preparedTwins`: preparation, then twin collapse. The census head of a store
lives on `prepare`'s residual store (`ContextualDependentCoverageReadersHalf.tower_census_head`). Twin collapse
**leaves every equation in place**: it maps each equation to one with the same left side and the same right side,
replacing the right annotation by the left one when the bounded comparison of types accepts them
(`collapseOne_left`, `collapseOne_right`, `collapseOne_homogeneous`). So every property of the three codes of an
equation (left annotation, left side, right side) is kept, and the collapsed equation is homogeneous once the
comparison accepts (`collapseOne_holds`, `collapseOne_same`).

In the tower:

* preparation is eventually constant (`tower_prepare_const`), so from some budget on the census head is one fixed
  equation of one fixed store, with normal codes (`tower_stable_census_head`);
* equal annotations are eventually compared successfully (`tower_compared`);
* hence from some budget on, the prepared store with homogeneous twins has a homogeneous equation whose three codes
  are the census head's (`tower_twins_keep`).

This is the bridge from the census to every reader that reads `preparedTwins` with homogeneous annotations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentTwinsUnder ContextualDependentConstantHeads ContextualDependentMillerClosure

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- Twin collapse keeps the left side and its annotation. -/
theorem collapseOne_left (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    (collapseOne facts roots heads algebra reducer fuel equation).1 = equation.1 := by
  unfold collapseOne
  split
  · rfl
  · split <;> rfl

/-- Twin collapse keeps the code of the right side. -/
theorem collapseOne_right (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    (collapseOne facts roots heads algebra reducer fuel equation).2.2.code = equation.2.2.code := by
  unfold collapseOne
  by_cases same : equation.2.1.code = equation.1.1.code
  · rw [if_pos same]
  · rw [if_neg same]
    split <;> rfl

/-- Once the comparison of the two annotations accepts, the right annotation of the collapsed equation is the left
one. -/
theorem collapseOne_homogeneous (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (compared : (Conversion.compareTypes facts roots heads algebra reducer fuel equation.1.1 equation.2.1).isSome) :
    (collapseOne facts roots heads algebra reducer fuel equation).2.1.code = equation.1.1.code := by
  unfold collapseOne
  split
  · assumption
  · obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp compared
    rw [computed]
    rfl

/-- **Twin collapse makes a compared equation homogeneous.** -/
theorem collapseOne_same (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (compared : (Conversion.compareTypes facts roots heads algebra reducer fuel equation.1.1 equation.2.1).isSome) :
    (collapseOne facts roots heads algebra reducer fuel equation).2.1.code =
      (collapseOne facts roots heads algebra reducer fuel equation).1.1.code := by
  rw [collapseOne_homogeneous facts roots heads algebra reducer fuel equation compared, collapseOne_left]

/-- **Twin collapse leaves the left annotation and both sides in place.** -/
theorem collapseOne_holds (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (holds : ∀ {n : Nat}, Tm Head n → Tm Head n → Tm Head n → Prop)
    (shape : holds equation.1.1.code equation.1.2.code equation.2.2.code) :
    holds (collapseOne facts roots heads algebra reducer fuel equation).1.1.code
      (collapseOne facts roots heads algebra reducer fuel equation).1.2.code
      (collapseOne facts roots heads algebra reducer fuel equation).2.2.code := by
  rw [collapseOne_left, collapseOne_right]
  exact shape

/-- The collapse of an equation of a store is an equation of the collapsed store. -/
theorem collapseOne_mem (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) :
    collapseOne facts roots heads algebra reducer fuel equation ∈
      (collapse facts roots heads algebra reducer fuel problem).remaining := by
  rw [collapse_remaining]
  exact List.mem_map_of_mem member

end General

section Tower

open ContextualDependentPatternFiring.Controls

/-- The tower's prepared store with homogeneous twins, at one budget. -/
abbrev towerPreparedTwins (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Update setting.levels problem :=
  preparedTwins (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel problem

/-- **The tower's preparation is eventually constant.** -/
theorem tower_prepare_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    ∃ threshold, ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem :=
  (ContextualDependentFragment.prepare_const (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads problem).spec

/-- **Equal annotations are eventually compared successfully** by the tower's twin collapse. -/
theorem tower_compared {Θ : Context setting.R} (equation : Equation (TotalTerm Θ))
    (types : TypeEq setting.R Θ.raw equation.1.1.code equation.2.1.code) :
    ∃ bound, ∀ larger, bound ≤ larger →
      (Conversion.compareTypes (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        ContextualDependentInversion.Controls.reducer larger equation.1.1 equation.2.1).isSome := by
  obtain ⟨bound, result, stable⟩ := ContextualDependentExecutableDiscovery.compareTypes_eventually
    (fun _ => (0 : Nat)) equation.1.1 equation.2.1 types
  exact ⟨bound, fun larger enough => Option.isSome_iff_exists.mpr ⟨result, stable larger enough⟩⟩

/-- Twin collapse at one budget, on a preparation equal to a fixed one. -/
theorem twins_keep_at {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (fuel : Nat) (prepared : Update setting.levels problem) (same : prepared = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (compared : (Conversion.compareTypes (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.reducer fuel equation.1.1 equation.2.1).isSome)
    (holds : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n → Tower.Tm n → Prop)
    (shape : holds equation.1.1.code equation.1.2.code equation.2.2.code) :
    ∃ twin ∈ (prepared.then (collapse (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentInversion.Controls.reducer fuel prepared.remaining)).remaining,
      twin.2.1.code = twin.1.1.code ∧ holds twin.1.1.code twin.1.2.code twin.2.2.code := by
  subst same
  exact ⟨_, collapseOne_mem (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer fuel member,
    collapseOne_same (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.reducer fuel equation compared,
    collapseOne_holds (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.reducer fuel equation holds shape⟩

/-- **Twin collapse leaves an equation of a constant preparation in place**: from some budget on, the prepared store
with homogeneous twins has a homogeneous equation with the same three codes. -/
theorem tower_twins_keep {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (holds : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n → Tower.Tm n → Prop)
    (shape : holds equation.1.1.code equation.1.2.code equation.2.2.code) :
    ∃ bound, ∀ larger, bound ≤ larger →
      ∃ twin ∈ (towerPreparedTwins larger problem).remaining, twin.2.1.code = twin.1.1.code ∧
        holds twin.1.1.code twin.1.2.code twin.2.2.code := by
  obtain ⟨compareBound, compared⟩ := tower_compared equation types
  exact ⟨max threshold compareBound, fun larger enough =>
    twins_keep_at larger (towerPrepare larger problem) (constant larger (le_of_max_le_left enough)) member
      (compared larger (le_of_max_le_right enough)) holds shape⟩

/-- **A census head of the tower on a preparation that no longer changes**: from some budget on preparation is
constant, and its store has a census head with normal codes. -/
theorem tower_stable_census_head {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller setting.levels problem) (nonempty : problem ≠ []) :
    ∃ threshold, (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) ∧
      ∃ equation ∈ (towerPrepare threshold problem).remaining,
        ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation ∧ CensusHead equation := by
  obtain ⟨constBound, constant⟩ := tower_prepare_const problem
  obtain ⟨headBound, head⟩ := tower_census_head permuted nonempty
  refine ⟨max constBound headBound, fun larger enough => ?_, head _ (le_max_right _ _)⟩
  rw [constant larger (le_of_max_le_left enough), constant _ (le_max_left _ _)]

end Tower

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
