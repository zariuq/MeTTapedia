import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Algebraic forgetting and literal stripping

An installation functor whose composite with stripping is naturally
isomorphic to the identity cannot induce a non-idempotent monad.  Algebraic
forgetting instead retains the free object's enlarged underlying carrier.

The results here apply to arbitrary categories.  They do not supply a monad
structure for a language transformation.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor

namespace Mettapedia.CategoryTheory.MonadResolutionObstruction

set_option autoImplicit false

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- Multiplication always has the unit at the transformed object as a
natural section. -/
def multiplicationSection (T : Monad C) : SplitEpi T.μ where
  section_ := (Functor.rightUnitor T.toFunctor).inv ≫
    whiskerLeft T.toFunctor T.η
  id := by
    ext X
    simp

/-- A monomorphic monad multiplication is invertible.  Thus requiring all
multiplications to be embeddings restricts monads to the idempotent case. -/
theorem multiplication_isIso_of_mono (T : Monad C) [Mono T.μ] :
    IsIso T.μ := by
  let : IsSplitEpi T.μ := IsSplitEpi.mk' (multiplicationSection T)
  exact isIso_of_mono_of_isSplitEpi T.μ

/-- Componentwise version, useful for faithful carrier observations. -/
theorem multiplication_app_isIso_of_mono (T : Monad C) (X : C)
    [Mono (T.μ.app X)] : IsIso (T.μ.app X) := by
  let : IsSplitEpi (T.μ.app X) := IsSplitEpi.mk'
    { section_ := T.η.app (T.obj X)
      id := T.left_unit X }
  exact isIso_of_mono_of_isSplitEpi (T.μ.app X)

/-- An invertible unit forces the entire multiplication to be invertible. -/
theorem multiplication_isIso_of_unit (T : Monad C) [IsIso T.η] :
    IsIso T.μ := by
  have : ∀ X : C, IsIso (T.μ.app X) := fun X => by
    have equality := IsIso.inv_eq_of_hom_inv_id (T.left_unit X)
    rw [← equality]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

variable {D : Type u'} [Category.{v'} D]
  {Install : C ⥤ D} {Forget : D ⥤ C}

/-- If forgetting installation literally returns the source up to a natural
isomorphism, both structural maps of the induced monad are isomorphisms. -/
theorem induced_unit_and_multiplication_isIso
    (adj : Install ⊣ Forget) (stripping : Install ⋙ Forget ≅ 𝟭 C) :
    IsIso adj.toMonad.η ∧ IsIso adj.toMonad.μ := by
  have : IsIso adj.toMonad.η := adj.isIso_unit_of_iso stripping
  exact ⟨inferInstance, multiplication_isIso_of_unit adj.toMonad⟩

/-- A non-idempotent induced monad rules out a natural identity round trip
for the proposed algebraic forgetful functor. -/
theorem no_identity_round_trip_of_noninvertible_multiplication
    (adj : Install ⊣ Forget) (noninvertible : ¬ IsIso adj.toMonad.μ) :
    ¬ Nonempty (Install ⋙ Forget ≅ 𝟭 C) := by
  rintro ⟨stripping⟩
  exact noninvertible
    (induced_unit_and_multiplication_isIso adj stripping).2

#print axioms multiplication_isIso_of_mono
#print axioms multiplication_app_isIso_of_mono
#print axioms multiplication_isIso_of_unit
#print axioms induced_unit_and_multiplication_isIso
#print axioms no_identity_round_trip_of_noninvertible_multiplication

end Mettapedia.CategoryTheory.MonadResolutionObstruction
