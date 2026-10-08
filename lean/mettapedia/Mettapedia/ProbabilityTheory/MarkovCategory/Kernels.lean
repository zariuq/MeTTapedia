import Mettapedia.ProbabilityTheory.MarkovCategory
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Kernel Instance for `MarkovCategoryCore`

This file instantiates `MarkovCategoryCore` for measurable spaces with
Markov kernels as morphisms.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory

open MeasureTheory
open _root_.Mettapedia.ProbabilityTheory

/-- Object type for the kernel Markov-category core: measurable spaces
packaged as `MeasCat` objects. -/
abbrev KernelMarkovObj : Type 1 := MeasCat

/-- Morphisms in the kernel Markov-category core. -/
abbrev KernelMarkovHom (X Y : KernelMarkovObj) : Type := ProbabilityTheory.Kernel X Y

/-- Binary-product object in the kernel Markov-category core. -/
abbrev kernelMarkovProdObj (X Y : KernelMarkovObj) : KernelMarkovObj := MeasCat.of (X × Y)

/-- Terminal object in the kernel Markov-category core. -/
abbrev kernelMarkovUnitObj : KernelMarkovObj := MeasCat.of PUnit

/-- `MarkovCategoryCore` instance specialized to measurable spaces and kernels. -/
noncomputable def kernelMarkovCategoryCore : MarkovCategoryCore where
  Obj := KernelMarkovObj
  Hom := KernelMarkovHom
  id := fun X => (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel X X)
  comp := fun {X Y Z} κ η => ProbabilityTheory.Kernel.comp η κ
  prod := kernelMarkovProdObj
  unit := kernelMarkovUnitObj
  copy := fun X => (ProbabilityTheory.Kernel.copy X)
  discard := fun X => (ProbabilityTheory.Kernel.discard X)
  id_comp := by
    intro X Y κ
    exact ProbabilityTheory.Kernel.comp_id κ
  comp_id := by
    intro X Y κ
    exact ProbabilityTheory.Kernel.id_comp κ
  comp_assoc := by
    intro W X Y Z f g h
    simpa using (ProbabilityTheory.Kernel.comp_assoc h g f)

/-- Kernel core check: discarding after copy equals discarding directly. -/
theorem kernelMarkovCategoryCore_copy_then_discard (X : KernelMarkovObj) :
    kernelMarkovCategoryCore.comp
        (kernelMarkovCategoryCore.copy X)
        (kernelMarkovCategoryCore.discard (kernelMarkovCategoryCore.prod X X)) =
      kernelMarkovCategoryCore.discard X := by
  change ProbabilityTheory.Kernel.comp
      (ProbabilityTheory.Kernel.discard (X × X))
      (ProbabilityTheory.Kernel.copy X) =
    ProbabilityTheory.Kernel.discard X
  exact ProbabilityTheory.Kernel.comp_discard
    (κ := (ProbabilityTheory.Kernel.copy X))

/-- Kernel core check: swap after copy is copy. -/
theorem kernelMarkov_swap_after_copy (X : KernelMarkovObj) :
    ProbabilityTheory.Kernel.comp
        (ProbabilityTheory.Kernel.swap X X)
        (ProbabilityTheory.Kernel.copy X) =
      ProbabilityTheory.Kernel.copy X := by
  exact ProbabilityTheory.Kernel.swap_copy (α := X)

end Mettapedia.ProbabilityTheory
