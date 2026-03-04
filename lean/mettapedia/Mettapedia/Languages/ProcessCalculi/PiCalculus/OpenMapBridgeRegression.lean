import Mettapedia.Languages.ProcessCalculi.PiCalculus.BranchingBisim

/-!
# π/ρ Open-Map Bridge Regression

Small theorem-level checks that pin the exported bridge equivalences.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem weakRestrictedBisim_pathBisim_regression
    (N : Finset String) (p q : Pattern) :
    WeakRestrictedBisim N p q ↔ PathBisim (PiRhoInst N) p q := by
  simpa using weakRestrictedBisim_iff_pathBisim N p q

theorem weakRestrictedBisimD_pathBisim_regression
    (N : Finset String) (p q : Pattern) :
    WeakRestrictedBisimD N p q ↔ PathBisim (PiRhoDerivedInst N) p q := by
  simpa using weakRestrictedBisimD_iff_pathBisim N p q

theorem branching_to_weak_regression
    (N : Finset String) {p q : Pattern} :
    BranchingBisimOM (PiRhoInst N) p q → WeakRestrictedBisim N p q :=
  weakRestrictedBisim_of_branchingOM N

theorem branching_to_weakD_regression
    (N : Finset String) {p q : Pattern} :
    BranchingBisimOM (PiRhoDerivedInst N) p q → WeakRestrictedBisimD N p q :=
  weakRestrictedBisimD_of_branchingOM N

end Mettapedia.Languages.ProcessCalculi.PiCalculus
