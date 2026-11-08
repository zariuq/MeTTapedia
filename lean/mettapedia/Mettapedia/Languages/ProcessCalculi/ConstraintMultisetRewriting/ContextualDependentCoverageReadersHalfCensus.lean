import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverageReadersHalf
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverageReaders

/-!
# The census on the prepared store

The readers of the flexible round read the **prepared** store, so a census of the original store must be carried to
the prepared one. Preparation keeps the permuted class on a strongly normalizing package (`prepare_keeps`) and keeps
the number of equations, so a nonempty store of the class has, on its prepared store, an equation with equal
annotations whose pairs of normal forms of opened sides are all census kinds (`PermutedMiller.exists_head`). For the
tower, from some budget on, every annotation and side of the prepared store is normal (R114's `prepared_normal`), so
at every larger budget the census head of the prepared store has normal codes (`tower_census_head`).

This is the common first step of the census half of coverage: what remains is, for each census kind of such an
equation, that one of R110's readers reads it (`ContextualDependentCoverageReadersHalf.Reads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentShortClosure ContextualDependentMillerClosure

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

/-- **A census head**: an equation with equal annotations, every pair of normal forms of whose opened sides is a
census kind. -/
def CensusHead {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  TypeEq rules Θ.raw equation.1.1.code equation.2.1.code ∧
    ∀ {left right : Tm Head (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)},
      Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        equation.1.2.code) left → Normal rules left →
      Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        equation.2.2.code) right → Normal rules right →
      Kind (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) left right

theorem PermutedMiller.exists_census_head [DecidableEq Head] {levels : LevelModel rules L} {Θ : Context rules}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller levels problem) (nonempty : problem ≠ []) :
    ∃ equation ∈ problem, CensusHead equation := by
  obtain ⟨equation, member, types, kinds⟩ := ContextualDependentMillerClosure.PermutedMiller.exists_head permuted
    nonempty
  exact ⟨equation, member, types, kinds⟩

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4 ContextualDependentCumulativeClosure

/-- The tower's preparation at one budget. -/
abbrev towerPrepare (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    ContextualDependentUpdate.Update setting.levels problem :=
  ContextualDependentNormalizing.prepare (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads fuel problem

/-- **The tower's prepared store has a census head with normal codes**, at every large budget, for every nonempty
store of the permuted class. -/
theorem tower_census_head {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller setting.levels problem) (nonempty : problem ≠ []) :
    ∃ bound, ∀ larger, bound ≤ larger →
      ∃ equation ∈ (towerPrepare larger problem).remaining,
        ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation ∧ CensusHead equation := by
  obtain ⟨bound, normal⟩ := ContextualDependentNormalizing.prepared_normal (fun _ => (0 : Nat)) problem
  refine ⟨bound, fun larger enough => ?_⟩
  have keeps := prepare_keeps (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing larger problem permuted
  have lengths := congrArg Prod.snd (ContextualDependentNormalizing.prepare_size (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads larger problem)
  have prepared : (towerPrepare larger problem).remaining ≠ [] := by
    intro empty
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    change (towerPrepare larger problem).remaining.length = problem.length at lengths
    rw [← lengths, empty]
    rfl
  obtain ⟨equation, member, head⟩ := PermutedMiller.exists_census_head keeps prepared
  exact ⟨equation, member, (normal larger enough).2 equation member, head⟩

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
