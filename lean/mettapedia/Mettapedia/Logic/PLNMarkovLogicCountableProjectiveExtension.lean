import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Restriction
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification

/-!
# Countable Boolean Projective Extension Frontend

This module implements the high-confidence bridge from arbitrary projective
families over a countable atom type to the prefix-indexed families over `ℕ`
that Mathlib's Ionescu-Tulcea/projective-limit machinery expects.

The council-backed strategy is:

1. reindex finite-dimensional marginals along an enumeration `ℕ ≃ Atom`,
2. package the reindexed family as prefix measures on `Iic n`,
3. prove those prefix measures satisfy the projective compatibility law.

This does not yet solve the full infinite-MLN existence theorem.  It isolates a
generic countable-Boolean extension layer that the infinite-MLN limit-family
work can instantiate cleanly.
-/

namespace Mettapedia.Logic.PLNMarkovLogicCountableProjectiveExtension

open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification

/-- Constant Bool-valued coordinates over an atom type. -/
abbrev BoolCoord (Atom : Type*) (_ : Atom) := Bool

/-- Constant Bool-valued coordinates over `ℕ`. -/
abbrev NatBoolCoord (_ : ℕ) := Bool

section Reindex

variable {Atom : Type*}

/-- The enumeration `e : ℕ ≃ Atom` restricts to an equivalence between the
prefix `Iic n` and its image in `Atom`. -/
noncomputable def prefixEquiv
    (e : ℕ ≃ Atom) (n : ℕ) :
    Finset.Iic n ≃ (Finset.Iic n).map e.toEmbedding where
  toFun i := ⟨e i, by
    refine Finset.mem_map.mpr ?_
    exact ⟨i, i.2, by simp⟩⟩
  invFun a := ⟨e.symm a, by
    simpa [Finset.mem_map_equiv] using a.2⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

/-- Reindex a finite-dimensional Boolean marginal along an enumeration `ℕ ≃ Atom`,
restricted to the prefix `Iic n`. -/
noncomputable def prefixFamily
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    (n : ℕ) : Measure (∀ i : Finset.Iic n, NatBoolCoord i) := by
  classical
  exact
    (P ((Finset.Iic n).map e.toEmbedding)).map
      ((MeasurableEquiv.piCongrLeft
        (fun i : ((Finset.Iic n).map e.toEmbedding) ↦ Bool)
        (prefixEquiv e n)).symm)

instance prefixFamily_isProbability
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (n : ℕ) :
    IsProbabilityMeasure (prefixFamily e P n) := by
  classical
  unfold prefixFamily
  exact Measure.isProbabilityMeasure_map
    ((MeasurableEquiv.piCongrLeft
      (fun i : ((Finset.Iic n).map e.toEmbedding) ↦ Bool)
      (prefixEquiv e n)).symm.measurable.aemeasurable)

/-- The reindexed prefix family satisfies the projective compatibility law on
initial segments of `ℕ`. -/
theorem prefixFamily_projective
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    {a b : ℕ} (hab : a ≤ b) :
    (prefixFamily e P b).map (Preorder.frestrictLe₂ (π := NatBoolCoord) hab) =
      prefixFamily e P a := by
  classical
  let Ia : Finset Atom := (Finset.Iic a).map e.toEmbedding
  let Ib : Finset Atom := (Finset.Iic b).map e.toEmbedding
  have hIaIb : Ia ⊆ Ib := by
    dsimp [Ia, Ib]
    exact Finset.map_subset_map.mpr (Finset.Iic_subset_Iic.mpr hab)
  have hPab : P Ia = (P Ib).map (Finset.restrict₂ hIaIb) := hP Ib Ia hIaIb
  rw [show prefixFamily e P b =
      (P Ib).map
        ((MeasurableEquiv.piCongrLeft
          (fun i : Ib ↦ Bool)
          (prefixEquiv e b)).symm) by
        simp [prefixFamily, Ib, BoolCoord, NatBoolCoord]]
  rw [show prefixFamily e P a =
      (P Ia).map
        ((MeasurableEquiv.piCongrLeft
          (fun i : Ia ↦ Bool)
          (prefixEquiv e a)).symm) by
        simp [prefixFamily, Ia, BoolCoord, NatBoolCoord]]
  have hcomp :
      (Preorder.frestrictLe₂ (π := NatBoolCoord) hab) ∘
          ⇑((MeasurableEquiv.piCongrLeft
            (fun i : Ib ↦ Bool)
            (prefixEquiv e b)).symm)
        =
      ⇑((MeasurableEquiv.piCongrLeft
          (fun i : Ia ↦ Bool)
          (prefixEquiv e a)).symm) ∘
        (Finset.restrict₂ (π := fun _ : Atom => Bool) hIaIb) := by
    ext x i
    rfl
  rw [hPab]
  rw [Measure.map_map]
  · rw [Measure.map_map]
    · simpa [Function.comp] using congrArg (fun f => Measure.map f (P Ib)) hcomp
    · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

/-- The prefix family obtained from a countable projective family induces a
projective family on arbitrary finite subsets of `ℕ`. -/
theorem isProjectiveMeasureFamily_inducedPrefix
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    MeasureTheory.IsProjectiveMeasureFamily
      (MeasureTheory.inducedFamily (μ := prefixFamily e P)) := by
  exact MeasureTheory.isProjectiveMeasureFamily_inducedFamily
    (μ := prefixFamily e P)
    (fun a b hab => prefixFamily_projective e P hP hab)

/-- Transport a measure on `ℕ → Bool` back to an infinite Boolean world over
atoms via the enumeration `ℕ ≃ Atom`. -/
noncomputable def transportMeasure
    (e : ℕ ≃ Atom)
    (μ : Measure (ℕ → Bool)) :
    Measure (InfiniteWorld Atom) :=
  μ.map (MeasurableEquiv.piCongrLeft (fun _ : Atom => Bool) e)

end Reindex

end Mettapedia.Logic.PLNMarkovLogicCountableProjectiveExtension
