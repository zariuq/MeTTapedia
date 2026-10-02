import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Data.Set.Image
import Mathlib.Data.Setoid.Basic

/-!
# Descent of predicates: the two liftings

A predicate on detailed states is a predicate on views only when it is constant
on the fibres of the view (`Mettapedia.GSLT.Core.NonFactorization`).  When it
is not, there are two ways to lift it to views, and they differ: "some state
with this view satisfies it" and "every state with this view satisfies it".
These are the image and the universal image of the predicate along the view,
the left and the right adjoint of preimage.

* `ConstantOnFibers.iff`, `constantOnFibers_of_iff`: fibre-constancy of a
  predicate, as an equivalence of its values.
* **Kernel form**: a function is constant on the fibres of a view exactly when
  the kernel of the view is contained in its own
  (`constantOnFibers_iff_ker_le`).
* **The two liftings agree exactly on descending predicates**: a predicate is
  constant on fibres exactly when its image is contained in its universal
  image (`constantOnFibers_iff_image_subset_kernImage`).
* Control: on the two truth values viewed through the constant view, the
  predicate "is true" has image the whole view and empty universal image
  (`Control.image_ne_kernImage`), and a constant predicate has the same two
  liftings (`Control.constant_image_subset_kernImage`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Mettapedia.GSLT.Core.NonFactorization

universe u v w

section Predicates

variable {A : Sort u} {S : Sort v} {shadow : A → S} {predicate : A → Prop}

theorem ConstantOnFibers.iff (constant : ConstantOnFibers shadow predicate) {a b : A}
    (sameShadow : shadow a = shadow b) : predicate a ↔ predicate b :=
  iff_of_eq (constant a b sameShadow)

theorem constantOnFibers_of_iff
    (agree : ∀ a b, shadow a = shadow b → (predicate a ↔ predicate b)) :
    ConstantOnFibers shadow predicate :=
  fun a b sameShadow => propext (agree a b sameShadow)

end Predicates

section Kernels

variable {A : Type u} {S : Type v} {V : Type w}

/-- **Kernel form of fibre-constancy.** -/
theorem constantOnFibers_iff_ker_le (shadow : A → S) (invariant : A → V) :
    ConstantOnFibers shadow invariant ↔ Setoid.ker shadow ≤ Setoid.ker invariant :=
  ⟨fun constant _ _ sameShadow => constant _ _ sameShadow,
    fun le _ _ sameShadow => le sameShadow⟩

end Kernels

section Liftings

variable {A : Type u} {S : Type v}

/-- **A predicate is constant on fibres exactly when its two liftings agree**:
whatever view is reached by a state satisfying it is reached only by states
satisfying it. -/
theorem constantOnFibers_iff_image_subset_kernImage (shadow : A → S) (predicate : A → Prop) :
    ConstantOnFibers shadow predicate ↔
      shadow '' {a | predicate a} ⊆ Set.kernImage shadow {a | predicate a} := by
  constructor
  · rintro constant _ ⟨a, holds, rfl⟩ b sameShadow
    exact (ConstantOnFibers.iff constant sameShadow).mpr holds
  · intro included
    refine constantOnFibers_of_iff fun a b sameShadow => ⟨fun holds => ?_, fun holds => ?_⟩
    · exact included ⟨a, holds, rfl⟩ sameShadow.symm
    · exact included ⟨b, holds, rfl⟩ sameShadow

end Liftings

namespace Control

/-- The view that forgets everything. -/
def forgetAll : Bool → Unit :=
  fun _ => ()

theorem image_ne_kernImage :
    () ∈ forgetAll '' {value | value = true} ∧
      () ∉ Set.kernImage forgetAll {value | value = true} :=
  ⟨⟨true, rfl, rfl⟩, fun all => Bool.noConfusion (all (x := false) rfl)⟩

theorem not_constantOnFibers : ¬ ConstantOnFibers forgetAll (fun value => value = true) :=
  (NonTrivialFiber.ofProp (shadow := forgetAll) (invariant := fun value => value = true)
    (a := true) (b := false) rfl rfl Bool.noConfusion).not_constantOnFibers

theorem constant_image_subset_kernImage :
    forgetAll '' {_value | True} ⊆ Set.kernImage forgetAll {_value | True} :=
  (constantOnFibers_iff_image_subset_kernImage forgetAll fun _ => True).mp fun _ _ _ => rfl

end Control

end Mettapedia.GSLT.Scope
