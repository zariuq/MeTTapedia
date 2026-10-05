import Mettapedia.TypeTheory.PresheafDependentIdentity
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Controls for the dependent family--slice comparison

The family of finite sets has an empty fibre at zero and two distinct
values at two. Both the slice comparison and dependent identity retain
those values, whereas the base projection alone identifies them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSliceControls

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafSlice PresheafDependentIdentity

abbrev Context := Discrete Unit

def base : Face Context := (Functor.const _).obj Nat

def values : Face Context := (Functor.const _).obj (Σ n : Nat, Fin n)

def projection : values ⟶ base where
  app _ := TypeCat.ofHom Sigma.fst
  naturality := by intros; rfl

def point : Contextᵒᵖ := Opposite.op (Discrete.mk ())

abbrev finiteFibre (n : Nat) :=
  ((fibreFunctor base).obj (Over.mk projection)).obj ⟨point, n⟩

/-- The zero fibre is genuinely empty. -/
theorem zeroFibre_empty : IsEmpty (finiteFibre 0) := by
  refine ⟨?_⟩
  rintro ⟨⟨n, index⟩, h⟩
  change n = 0 at h
  subst n
  exact Fin.elim0 index

def firstValue : finiteFibre 2 := ⟨⟨2, 0⟩, rfl⟩

def secondValue : finiteFibre 2 := ⟨⟨2, 1⟩, rfl⟩

/-- A single nonconstant family has both an empty fibre and a fibre
with two distinguishable inhabitants. -/
theorem twoFibre_distinct : firstValue ≠ secondValue := by
  intro h
  have indices := congrArg (fun x : finiteFibre 2 => x.val.2.val) h
  exact Nat.zero_ne_one indices

/-- The slice counit reconstructs each original finite-set element. -/
theorem slice_counit_retains (n : Nat) (index : Fin n) :
    ((counitIso base).hom.app (Over.mk projection)).left.app point
      ⟨n, ⟨⟨n, index⟩, rfl⟩⟩ = ⟨n, index⟩ := rfl

/-- Projecting to the contextual index discards a real distinction. -/
theorem projection_forgets_value :
    firstValue.val ≠ secondValue.val ∧
      projection.app point firstValue.val = projection.app point secondValue.val := by
  constructor
  · intro h
    exact twoFibre_distinct (Subtype.ext h)
  · rfl

/-- Actual dependent application returns each finite-set value exactly. -/
theorem dependent_identity_retains (n : Nat) (index : Fin n) :
    (Limits.pullback.fst projection projection).app point
      ((PresheafDependentAdjunction.evaluation projection
        ((Over.pullback projection).obj (Over.mk projection))).left.app point
        (((Over.pullback projection).map (identityFunction projection)).left.app point
          ((argumentMap projection).app point ⟨n, index⟩))) = ⟨n, index⟩ :=
  identity_retains_value projection point ⟨n, index⟩

end Mettapedia.TypeTheory.DisplayedPresheafSliceControls
