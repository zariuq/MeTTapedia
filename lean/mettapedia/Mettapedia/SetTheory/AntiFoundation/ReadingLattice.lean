import Mettapedia.SetTheory.AntiFoundation.ReadingStep

/-!
# Readings are the canonical quotients

A setoid is a fixed point of the child-class step exactly when the quotient map is a
canonical decoration of the quotient's own membership and that membership is weakly
extensional. The kernel of a canonical decoration into any weakly extensional membership
is such a fixed point. Those fixed points form a complete lattice: the least one relates
the nodes that every reading identifies, and the greatest one relates the nodes that some
reading identifies.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT.QuotientObservers
open Function (fixedPoints)

universe u

variable {α : Type u}

theorem isDecoration_quotient_mk_iff (edge : Edge α) (R : Setoid α) :
    IsDecoration edge (quotientMem edge R) (Quotient.mk R) ↔
      IsBisimulation edge edge (⇑R) := by
  constructor
  · intro hdec a b hab
    constructor
    · intro a' ha'
      have hmem : quotientMem edge R (Quotient.mk R a') (Quotient.mk R b) := by
        change quotientEdge edge R (Quotient.mk R b) (Quotient.mk R a')
        rw [← Quotient.sound hab]
        exact quotientEdge_mk_of_edge edge R ha'
      obtain ⟨b', hb', heq⟩ := (hdec b (Quotient.mk R a')).mp hmem
      exact ⟨b', hb', Quotient.exact heq⟩
    · intro b' hb'
      have hmem : quotientMem edge R (Quotient.mk R b') (Quotient.mk R a) := by
        change quotientEdge edge R (Quotient.mk R a) (Quotient.mk R b')
        rw [Quotient.sound hab]
        exact quotientEdge_mk_of_edge edge R hb'
      obtain ⟨a', ha', heq⟩ := (hdec a (Quotient.mk R b')).mp hmem
      exact ⟨a', ha', Quotient.exact heq.symm⟩
  · intro hbis a y
    have hR : R ≤ step edge R := (le_step_iff_isBisimulation edge R).mpr hbis
    constructor
    · intro hy
      obtain ⟨b, hb, hy⟩ := (quotientEdge_mk_iff edge R hR a y).mp hy
      exact ⟨b, hb, hy.symm⟩
    · intro ⟨b, hb, hy⟩
      exact hy ▸ quotientEdge_mk_of_edge edge R hb

/-- The kernel of a canonical decoration into a weakly extensional membership is a reading.
The carrier of that membership need not be the quotient. -/
theorem reading_of_canonicalDecoration {V : Type u} (edge : Edge α) (R : Setoid α)
    (mem : MemRel V) (d : α → V) (hcan : CanonicalDecoration edge (⇑R) mem d)
    (hwe : WeaklyExtensional (memChild mem)) : step edge R = R := by
  apply le_antisymm
  · intro a b hab
    have hsame : SameChildren edge (⇑R) a b := (step_apply edge R a b).mp hab
    apply hcan.reflects
    apply hwe
    intro y
    constructor
    · intro hy
      obtain ⟨a', ha', hya⟩ := (hcan.decoration a y).mp hy
      obtain ⟨b', hb', hR⟩ := hsame.1 a' ha'
      exact (hcan.decoration b y).mpr ⟨b', hb', hya.trans (hcan.respects _ _ hR)⟩
    · intro hy
      obtain ⟨b', hb', hyb⟩ := (hcan.decoration b y).mp hy
      obtain ⟨a', ha', hR⟩ := hsame.2 b' hb'
      exact (hcan.decoration a y).mpr ⟨a', ha', hyb.trans (hcan.respects _ _ hR).symm⟩
  · intro a b hab
    apply (step_apply edge R a b).mpr
    have hd : d a = d b := hcan.respects _ _ hab
    constructor
    · intro a' ha'
      have hmem : mem (d a') (d b) := hd ▸ (hcan.decoration a (d a')).mpr ⟨a', ha', rfl⟩
      obtain ⟨b', hb', heq⟩ := (hcan.decoration b (d a')).mp hmem
      exact ⟨b', hb', hcan.reflects _ _ heq⟩
    · intro b' hb'
      have hmem : mem (d b') (d a) := hd ▸ (hcan.decoration b (d b')).mpr ⟨b', hb', rfl⟩
      obtain ⟨a', ha', heq⟩ := (hcan.decoration a (d b')).mp hmem
      exact ⟨a', ha', hcan.reflects _ _ heq.symm⟩

/-- A setoid is a reading exactly when the quotient map is a canonical decoration of the
quotient membership and that membership is weakly extensional. -/
theorem reading_iff_canonicalDecoration (edge : Edge α) (R : Setoid α) :
    step edge R = R ↔
      CanonicalDecoration edge (⇑R) (quotientMem edge R) (Quotient.mk R) ∧
        WeaklyExtensional (memChild (quotientMem edge R)) := by
  constructor
  · intro hfix
    have hle : R ≤ step edge R := hfix.symm.le
    have hge : step edge R ≤ R := hfix.le
    have hbis : IsBisimulation edge edge (⇑R) := (le_step_iff_isBisimulation edge R).mp hle
    refine ⟨?_, ?_⟩
    · refine ⟨(isDecoration_quotient_mk_iff edge R).mpr hbis, ?_, ?_⟩
      · intro a b hab
        exact Quotient.sound hab
      · intro a b hab
        exact Quotient.exact hab
    · rw [memChild_quotientMem]
      exact (step_le_iff_quotient_weaklyExtensional edge R hle).mp hge
  · intro ⟨hcan, hwe⟩
    exact reading_of_canonicalDecoration edge R (quotientMem edge R) (Quotient.mk R) hcan hwe

/-- Knaster–Tarski: the readings, the fixed points of `step`, form a complete lattice. -/
@[instance_reducible]
noncomputable def readingLattice (edge : Edge α) :
    CompleteLattice (fixedPoints (step edge)) :=
  inferInstance

theorem related_every_reading_iff_lfp (edge : Edge α) (a b : α) :
    (∀ R : fixedPoints (step edge), (↑R : Setoid α) a b) ↔ (step edge).lfp a b := by
  constructor
  · intro h
    exact h ⟨(step edge).lfp, (step edge).isFixedPt_lfp⟩
  · intro h R
    exact ((step edge).lfp_le_fixed R.2) h

theorem related_some_reading_iff_gfp (edge : Edge α) (a b : α) :
    (∃ R : fixedPoints (step edge), (↑R : Setoid α) a b) ↔ (step edge).gfp a b := by
  constructor
  · rintro ⟨R, hab⟩
    exact ((step edge).le_gfp R.2.symm.le) hab
  · intro h
    exact ⟨⟨(step edge).gfp, (step edge).isFixedPt_gfp⟩, h⟩

end Mettapedia.SetTheory.AntiFoundation
