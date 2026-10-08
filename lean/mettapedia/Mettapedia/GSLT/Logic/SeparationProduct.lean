import Mettapedia.GSLT.Logic.SeparationAlgebra
import Mathlib.Algebra.Group.Prod

/-!
# Products of separation algebras

Two separation algebras side by side form one, componentwise: a pair of
resources is separate from another pair when each component is separate from
its partner, and pairs are added componentwise.  Every law holds because it
holds in each component.

A resource with two kinds of parts uses this: a memory block, for instance,
holds a header and a family of cells.  The header and the cells are owned
independently, so a block resource can hold the header without any cell, or
some cells without the header.

## Examples

* **Positive.**  Owning the left component of a pair of exclusive cells is
  separate from owning the right component, and the two combine into the pair
  owning both (`excl_pair_split`).
* **Negative.**  Two pairs that both own the left component are not separate,
  whatever they hold on the right (`excl_pair_not_separate`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.SeparationAlgebra

open SepAlgebra

universe u v

variable {α : Type u} {β : Type v} [Zero α] [Add α] [SepAlgebra α]
  [Zero β] [Add β] [SepAlgebra β]

/-- Pairs of resources, componentwise. -/
instance instProd : SepAlgebra (α × β) where
  Separate x y := x.1 ## y.1 ∧ x.2 ## y.2
  separate_zero x := ⟨separate_zero x.1, separate_zero x.2⟩
  separate_symm separate := ⟨separate_symm separate.1, separate_symm separate.2⟩
  add_zero x := Prod.ext (SepAlgebra.add_zero x.1) (SepAlgebra.add_zero x.2)
  add_comm separate :=
    Prod.ext (SepAlgebra.add_comm separate.1) (SepAlgebra.add_comm separate.2)
  add_assoc separateXY separateYZ separateXZ :=
    Prod.ext (SepAlgebra.add_assoc separateXY.1 separateYZ.1 separateXZ.1)
      (SepAlgebra.add_assoc separateXY.2 separateYZ.2 separateXZ.2)
  separate_of_separate_add separate separateParts :=
    ⟨separate_of_separate_add separate.1 separateParts.1,
      separate_of_separate_add separate.2 separateParts.2⟩
  separate_add_of_separate_add separate separateParts :=
    ⟨separate_add_of_separate_add separate.1 separateParts.1,
      separate_add_of_separate_add separate.2 separateParts.2⟩

theorem separate_prod_iff {x y : α × β} : x ## y ↔ x.1 ## y.1 ∧ x.2 ## y.2 :=
  Iff.rfl

/-! ## Controls -/

section Controls

variable {γ : Type u}

/-- **Positive control**: the two components of a pair of exclusive cells are
owned separately, and together they own the pair. -/
theorem excl_pair_split (a b : γ) :
    ((Excl.own a, Excl.empty) : Excl γ × Excl γ) ## (Excl.empty, Excl.own b) ∧
      ((Excl.own a, Excl.empty) : Excl γ × Excl γ) + (Excl.empty, Excl.own b) =
        (Excl.own a, Excl.own b) :=
  ⟨⟨Or.inr rfl, Or.inl rfl⟩, rfl⟩

/-- **Negative control**: two pairs that both own the left component are never
separate, whatever their right components are. -/
theorem excl_pair_not_separate (a a' : γ) (right right' : Excl γ) :
    ¬ ((Excl.own a, right) : Excl γ × Excl γ) ## (Excl.own a', right') :=
  fun separate => Excl.not_separate_own a a' separate.1

end Controls

end Mettapedia.GSLT.SeparationAlgebra
