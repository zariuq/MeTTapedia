import Foundation.FirstOrder.Ultraproduct
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore

/-!
# Łoś transfer for ultrainfinitist truth

Ultrainfinitist truth (`UltraTrue`) of a first-order sentence along a family of
structures is truth in their ultraproduct (`ultraTrue_iff_uprod`); in particular a
structure is elementarily equivalent to every ultrapower of itself
(`ultrapower_elementary`).  These are thin restatements of
`LO.FirstOrder.models_Uprod` in the wrapper vocabulary.  They are kept apart from
`UltrainfinitismCore` because the first-order library declares global syntax
tokens that the operational core must not inherit.
-/

universe u

namespace Mettapedia.Logic.Metaphysics

variable {I : Type u}

/-! ## Łoś transfer -/

section Los

open LO FirstOrder FirstOrder.Structure

variable {L : Language.{u}} {A : I → Type u} [(i : I) → Structure L (A i)]
  [Nonempty I] [(i : I) → Nonempty (A i)]

/-- **Łoś transfer**, wrapper form: ultrainfinitist truth of a first-order sentence
along the family IS truth in the ultraproduct — the invariant bridge between the
coordinates and the One. -/
theorem ultraTrue_iff_uprod (𝓤 : Ultrafilter I) (φ : Sentence L) :
    UltraTrue 𝓤 (fun i => A i ⊧ₘ φ) ↔ (Uprod A 𝓤) ⊧ₘ φ := by
  rw [models_Uprod]
  exact Iff.rfl

/-- A structure is elementarily equivalent to every ultrapower of itself: the One built
over constant coordinates validates exactly the coordinate's first-order truths. -/
theorem ultrapower_elementary {B : Type u} [Structure L B] [Nonempty B]
    (𝓤 : Ultrafilter I) (φ : Sentence L) :
    (Uprod (fun _ : I => B) 𝓤) ⊧ₘ φ ↔ B ⊧ₘ φ := by
  rw [← ultraTrue_iff_uprod]
  constructor
  · intro h
    obtain ⟨_, hi⟩ := Ultrafilter.nonempty_of_mem (Filter.eventually_iff.mp h)
    exact hi
  · intro h
    exact Filter.Eventually.of_forall fun _ => h

end Los

end Mettapedia.Logic.Metaphysics
