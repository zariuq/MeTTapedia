import Mettapedia.CategoryTheory.GeneralizedOpenMaps
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimDerived

/-!
# Weak Bisim ↔ Generalized Open-Map Path Bisim

Bridges existing `WeakRestrictedBisim` / `WeakRestrictedBisimD` definitions to a
shared generalized open-map style interface.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Observable names restricted to `N`. -/
abbrev ObsName (N : Finset String) := { x : String // x ∈ N }

/-- Generic open-map kit corresponding to `WeakRestrictedBisim`. -/
def PiRhoInst (N : Finset String) : BisimulationKit Pattern (ObsName N) where
  step := fun p q =>
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces p q)
  stepStar := fun p q =>
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar p q)
  step_sub_star := by
    intro p q hpq
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar.step
      (Classical.choice hpq)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar.refl q)⟩
  observable := fun p o => RhoObservableSC p (.fvar o.1)

/-- Generic open-map kit corresponding to `WeakRestrictedBisimD`. -/
def PiRhoDerivedInst (N : Finset String) : BisimulationKit Pattern (ObsName N) where
  step := fun p q => Nonempty (p ⇝ᵈ q)
  stepStar := fun p q => Nonempty (p ⇝ᵈ* q)
  step_sub_star := by
    intro p q hpq
    exact ⟨ReducesDerivedStar.step (Classical.choice hpq) (ReducesDerivedStar.refl q)⟩
  observable := fun p o => RhoObservableSC p (.fvar o.1)

theorem weakRestrictedBisim_iff_pathBisim
    (N : Finset String) (p q : Pattern) :
    WeakRestrictedBisim N p q ↔ PathBisim (PiRhoInst N) p q := by
  constructor
  · rintro ⟨R, hsym, hfwd, hobs, hpq⟩
    refine ⟨{ rel := R, symm := hsym, lift := ?_, obs := ?_ }, hpq⟩
    · intro p₁ q₁ hpq' p₂ hp₂
      exact hfwd p₁ q₁ hpq' p₂ hp₂
    · intro p₁ q₁ hpq' o hpo
      exact hobs p₁ q₁ hpq' o.1 o.2 hpo
  · rintro ⟨w, hpq⟩
    refine ⟨w.rel, w.symm, ?_, ?_, hpq⟩
    · intro p₁ q₁ hpq' p₂ hp₂
      exact w.lift hpq' hp₂
    · intro p₁ q₁ hpq' x hx hpo
      exact w.obs hpq' ⟨x, hx⟩ hpo

theorem weakRestrictedBisimD_iff_pathBisim
    (N : Finset String) (p q : Pattern) :
    WeakRestrictedBisimD N p q ↔ PathBisim (PiRhoDerivedInst N) p q := by
  constructor
  · rintro ⟨R, hsym, hfwd, hobs, hpq⟩
    refine ⟨{ rel := R, symm := hsym, lift := ?_, obs := ?_ }, hpq⟩
    · intro p₁ q₁ hpq' p₂ hp₂
      exact hfwd p₁ q₁ hpq' p₂ hp₂
    · intro p₁ q₁ hpq' o hpo
      exact hobs p₁ q₁ hpq' o.1 o.2 hpo
  · rintro ⟨w, hpq⟩
    refine ⟨w.rel, w.symm, ?_, ?_, hpq⟩
    · intro p₁ q₁ hpq' p₂ hp₂
      exact w.lift hpq' hp₂
    · intro p₁ q₁ hpq' x hx hpo
      exact w.obs hpq' ⟨x, hx⟩ hpo

end Mettapedia.Languages.ProcessCalculi.PiCalculus
