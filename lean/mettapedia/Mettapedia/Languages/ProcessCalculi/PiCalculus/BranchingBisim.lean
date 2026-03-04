import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimOpenMapBridge

/-!
# Branching/Stuttering Layer via Generalized Open Maps

Minimal explicit layer naming the standard correspondences:

- branching (history-preserving) side ↔ strong path bisimulation
- weak side ↔ path bisimulation
- branching implies weak
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Weak bisim in open-map form. -/
abbrev WeakBisimOM {α : Type _} {Obs : Type _} (K : BisimulationKit α Obs) (p q : α) : Prop :=
  PathBisim K p q

/-- Branching bisim in open-map form (minimal core). -/
abbrev BranchingBisimOM {α : Type _} {Obs : Type _} (K : BisimulationKit α Obs) (p q : α) : Prop :=
  StrongPathBisim K p q

/-- Stuttering branching bisim in open-map form (minimal core). -/
abbrev StutteringBranchingBisimOM {α : Type _} {Obs : Type _}
    (K : BisimulationKit α Obs) (p q : α) : Prop :=
  StrongPathBisim K p q

theorem stutteringBranching_iff_strongPathBisim
    {α : Type _} {Obs : Type _} (K : BisimulationKit α Obs) (p q : α) :
    StutteringBranchingBisimOM K p q ↔ StrongPathBisim K p q :=
  Iff.rfl

theorem weak_iff_pathBisim
    {α : Type _} {Obs : Type _} (K : BisimulationKit α Obs) (p q : α) :
    WeakBisimOM K p q ↔ PathBisim K p q :=
  Iff.rfl

theorem branching_implies_weak
    {α : Type _} {Obs : Type _} (K : BisimulationKit α Obs) {p q : α} :
    BranchingBisimOM K p q → WeakBisimOM K p q :=
  strongPathBisim_implies_pathBisim K

/-- Concrete π/ρ bridge: branching-style witness implies existing weak bisim. -/
theorem weakRestrictedBisim_of_branchingOM
    (N : Finset String) {p q : Pattern} :
    BranchingBisimOM (PiRhoInst N) p q → WeakRestrictedBisim N p q := by
  intro hBranch
  exact (weakRestrictedBisim_iff_pathBisim N p q).mpr (branching_implies_weak (PiRhoInst N) hBranch)

/-- Concrete derived π/ρ bridge: branching-style witness implies existing derived weak bisim. -/
theorem weakRestrictedBisimD_of_branchingOM
    (N : Finset String) {p q : Pattern} :
    BranchingBisimOM (PiRhoDerivedInst N) p q → WeakRestrictedBisimD N p q := by
  intro hBranch
  exact (weakRestrictedBisimD_iff_pathBisim N p q).mpr
    (branching_implies_weak (PiRhoDerivedInst N) hBranch)

end Mettapedia.Languages.ProcessCalculi.PiCalculus
