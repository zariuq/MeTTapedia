import Mettapedia.SetTheory.AntiFoundation.ReadingStep

/-!
# Least and greatest readings

The greatest fixed point of the child-class step is bisimilarity, on every graph.
The least fixed point is equality exactly when the graph is weakly extensional.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {α : Type u}

theorem step_bot_le_iff_weaklyExtensional (edge : Edge α) :
    step edge ⊥ ≤ ⊥ ↔ WeaklyExtensional edge := by
  constructor
  · intro hle a b hsame
    apply hle
    constructor
    · intro c hc
      exact ⟨c, (hsame c).mp hc, rfl⟩
    · intro c hc
      exact ⟨c, (hsame c).mpr hc, rfl⟩
  · intro hwe a b hab
    apply hwe
    intro c
    constructor
    · intro hc
      obtain ⟨d, hd, he⟩ := hab.1 c hc
      cases he
      exact hd
    · intro hc
      obtain ⟨d, hd, he⟩ := hab.2 c hc
      cases he
      exact hd

/-- The least fixed point is equality exactly on the weakly extensional graphs. -/
theorem lfp_eq_eq_iff_weaklyExtensional (edge : Edge α) :
    ⇑((step edge).lfp) = Eq ↔ WeaklyExtensional edge := by
  constructor
  · intro h
    have hlfp : (step edge).lfp = ⊥ := by
      apply Setoid.ext
      intro a b
      rw [Setoid.bot_def]
      exact Iff.of_eq (congrFun (congrFun h a) b)
    have hstep : step edge ⊥ = ⊥ := by
      simpa [hlfp] using (step edge).map_lfp
    exact (step_bot_le_iff_weaklyExtensional edge).mp hstep.le
  · intro hwe
    have hlfp : (step edge).lfp = ⊥ :=
      le_antisymm
        ((step edge).lfp_le ((step_bot_le_iff_weaklyExtensional edge).mpr hwe))
        bot_le
    ext a b
    rw [hlfp, Setoid.bot_def]

/-- The greatest fixed point is bisimilarity on every graph. -/
theorem gfp_eq_bisimilar (edge : Edge α) :
    (step edge).gfp = bisimilarSetoid edge := by
  apply le_antisymm
  · apply OrderHom.gfp_le
    intro R hR a b hab
    exact ((le_step_iff_isBisimulation edge R).mp hR).bisimilar hab
  · apply OrderHom.le_gfp
    exact (le_step_iff_isBisimulation edge (bisimilarSetoid edge)).mpr
      (RegularIdentification.bisimilarity edge).bisim

end Mettapedia.SetTheory.AntiFoundation
