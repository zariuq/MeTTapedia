import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Data.Fintype.Card

/-!
# Finite targets do not freely generate arbitrary recursive rule evidence

The endofunctor `X ↦ 1 + X` models a premise-free starting event and a
unary recursive event constructor. It has ordinary algebras in finite
types, but no initial algebra there: Lambek's lemma would make `1 + X`
isomorphic to `X`, contradicting finite cardinality. The existence of
finite limits and rule actions therefore does not by itself supply the
free recursive event construction inside every semantic target.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredFreeAlgebraBoundary

open CategoryTheory CategoryTheory.Limits

/-- One nullary event and one unary recursive event constructor. -/
def optionFunctor : FintypeCat ⥤ FintypeCat where
  obj X := FintypeCat.of (Option X)
  map f := FintypeCat.homMk (Option.map f)
  map_id X := by
    apply FintypeCat.hom_ext
    intro x
    cases x <;> rfl
  map_comp f g := by
    apply FintypeCat.hom_ext
    intro x
    cases x <;> rfl

/-- Finite algebras of this signature exist: the only state receives both
the initial event and all successor events. -/
def oneStateAlgebra : Endofunctor.Algebra optionFunctor where
  a := FintypeCat.of Unit
  str := FintypeCat.homMk (fun _ => ())

/-- This negative control already lives in a target with finite limits. -/
example : HasFiniteLimits FintypeCat := inferInstance

/-- Even finite coproducts do not produce the recursive free algebra. -/
example : HasFiniteColimits FintypeCat := inferInstance

/-- No finite algebra for the nullary/unary signature is initial. -/
theorem noInitial (A : Endofunctor.Algebra optionFunctor) :
    ¬ Nonempty (IsInitial A) := by
  rintro ⟨initial⟩
  let : Fintype A.a := FintypeCat.fintype
  have hIso : IsIso A.str := Endofunctor.Algebra.Initial.str_isIso initial
  have equivalent : Option A.a ≃ A.a :=
    FintypeCat.equivEquivIso.symm (asIso A.str)
  have cardEq := Fintype.card_congr equivalent
  simp only [Fintype.card_option] at cardEq
  omega

end Mettapedia.OSLF.Binding.CategoricalAuthoredFreeAlgebraBoundary
