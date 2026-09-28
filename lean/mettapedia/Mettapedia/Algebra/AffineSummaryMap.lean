import Mettapedia.Algebra.AffineMonoid

/-!
# Change of coefficients for affine summaries

A semiring homomorphism `φ : R →+* S` acts on affine summaries coefficientwise,
`map φ ⟨a, b⟩ = ⟨φ a, φ b⟩`. This file proves that the construction is a functor
from semirings to monoids that is compatible with the structure the affine
monoid carries.

* `map φ` is a monoid homomorphism. The image of an ordered product is the
  ordered product of the images (`map_list_prod`), and powers map to powers
  (`map_pow`).
* It is functorial (`map_id`, `map_comp`), and injective or surjective when
  `φ` is (`map_injective`, `map_surjective`).
* `φ` intertwines the actions (`act_map`): mapping the result of `f` equals
  acting by `map φ f` on the mapped state. In right-action notation,
  `φ (x <• f) = φ x <• map φ f` (`op_smul_map`). Consequently an ordered run
  maps to the run of the mapped updates (`run_map`, `act_prod_map`).
* Translations map to translations and scalings to scalings. Homogeneous
  matrices map entrywise (`matrix_map`).

The motivating instance is reduction modulo `m`, the ring homomorphism
`Int.castRingHom (ZMod m)`. An integer affine stream, reduced modulo `m`, is
the stream of reduced summaries acting on the reduced initial state.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.AffineSummary

open scoped RightActions

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]

/-- Change of coefficients along a semiring homomorphism, coefficientwise. It is
a monoid homomorphism for execution-order composition. -/
def map (φ : R →+* S) : AffineSummary R →* AffineSummary S where
  toFun f := ⟨φ f.scale, φ f.offset⟩
  map_one' := AffineSummary.ext φ.map_one φ.map_zero
  map_mul' f g := AffineSummary.ext (φ.map_mul _ _) <| by
    change φ (g.scale * f.offset + g.offset) = φ g.scale * φ f.offset + φ g.offset
    rw [φ.map_add, φ.map_mul]

@[simp] theorem scale_map (φ : R →+* S) (f : AffineSummary R) :
    (map φ f).scale = φ f.scale := rfl

@[simp] theorem offset_map (φ : R →+* S) (f : AffineSummary R) :
    (map φ f).offset = φ f.offset := rfl

@[simp] theorem map_mk (φ : R →+* S) (a b : R) : map φ ⟨a, b⟩ = ⟨φ a, φ b⟩ := rfl

/-- `φ` intertwines the actions: acting by `map φ f` on `φ x` is mapping `f.act x`. -/
@[simp] theorem act_map (φ : R →+* S) (f : AffineSummary R) (x : R) :
    (map φ f).act (φ x) = φ (f.act x) := by
  simp only [act, scale_map, offset_map, φ.map_add, φ.map_mul]

/-- `act_map` for the right action: `φ` is equivariant along `map φ`. -/
theorem op_smul_map (φ : R →+* S) (f : AffineSummary R) (x : R) :
    φ x <• map φ f = φ (x <• f) :=
  act_map φ f x

@[simp] theorem map_id : map (RingHom.id R) = MonoidHom.id (AffineSummary R) := rfl

theorem map_comp (ψ : S →+* T) (φ : R →+* S) : map (ψ.comp φ) = (map ψ).comp (map φ) := rfl

theorem map_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (map φ) :=
  fun _ _ h => AffineSummary.ext (hφ (congrArg scale h)) (hφ (congrArg offset h))

theorem map_surjective {φ : R →+* S} (hφ : Function.Surjective φ) :
    Function.Surjective (map φ) := by
  intro f
  obtain ⟨a, ha⟩ := hφ f.scale
  obtain ⟨b, hb⟩ := hφ f.offset
  exact ⟨⟨a, b⟩, AffineSummary.ext ha hb⟩

@[simp] theorem map_translation (φ : R →+* S) (b : R) :
    map φ (translation b) = translation (φ b) :=
  AffineSummary.ext φ.map_one rfl

@[simp] theorem map_scaling (φ : R →+* S) (a : R) :
    map φ (scaling a) = scaling (φ a) :=
  AffineSummary.ext rfl φ.map_zero

/-- Homogeneous coordinates commute with change of coefficients. -/
theorem matrix_map (φ : R →+* S) (f : AffineSummary R) :
    (map φ f).matrix = φ.mapMatrix f.matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- The mapped ordered product acts on the mapped state as the image of the
product's action. -/
theorem act_prod_map {ι : Type*} (φ : R →+* S) (coeff : ι → AffineSummary R) (items : List ι)
    (x : R) :
    (items.map fun i => map φ (coeff i)).prod.act (φ x) = φ ((items.map coeff).prod.act x) := by
  rw [← act_map, map_list_prod, List.map_map]
  rfl

/-- An ordered run maps to the run of the mapped updates. -/
theorem run_map (φ : R →+* S) (updates : List (AffineSummary R)) (x : R) :
    run (updates.map (map φ)) (φ x) = φ (run updates x) := by
  rw [run_eq_summary, run_eq_summary, ← map_list_prod, act_map]

end Mettapedia.Algebra.AffineSummary
