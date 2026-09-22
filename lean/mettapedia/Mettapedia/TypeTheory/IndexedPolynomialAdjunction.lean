import Mettapedia.TypeTheory.IndexedPolynomialCoalgebra
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The indexed free-algebra adjunction

The existing free plans are the free algebras of the actual indexed polynomial
endofunctor. Restriction to typed leaves is naturally inverse to the original
fold. The categorical monad is obtained from that adjunction, not from another
tree datatype or independently supplied monad laws.

This is the free-algebra adjunction for indexed polynomial plans. It is not
the language-extension adjunction in Finding Mind Proposition 19.1.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

open CategoryTheory

universe u

variable {Base : Type u} {Index : Base → Type u}
variable (P : IndexedPolynomial.{u, u, u, u} Base Index)

namespace FreeAdjunction

/-- Read a categorical algebra through the original pointwise algebra interface. -/
def pointwiseAlgebra (A : Endofunctor.Algebra P.endofunctor) : P.Algebra A.a where
  act := fun base index => A.str base index

/-- The free carrier and constructor action are the existing free plans. -/
def freeAlgebra (H : Family Base Index) : Endofunctor.Algebra P.endofunctor where
  a := P.Free H
  str := fun base index => ↾((Free.algebra P).act base index)

noncomputable section

/-- Relabeling leaves is an algebra morphism, with every node retained. -/
def freeMap {H K : Family Base Index} (mapping : H ⟶ K) :
    freeAlgebra P H ⟶ freeAlgebra P K where
  f := fun base index => ↾(Free.map P (fun b i => mapping b i) base index)
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro layer
    cases layer
    rfl

/-- The original free-plan map, packaged as a functor into polynomial algebras. -/
def freeFunctor : Family Base Index ⥤ Endofunctor.Algebra P.endofunctor where
  obj := freeAlgebra P
  map mapping := freeMap P mapping
  map_id H := by
    apply Endofunctor.Algebra.ext
    funext base index
    apply ConcreteCategory.hom_ext
    intro plan
    exact Free.map_id P plan
  map_comp earlier later := by
    apply Endofunctor.Algebra.ext
    funext base index
    apply ConcreteCategory.hom_ext
    intro plan
    exact (Free.map_comp P (fun b i => earlier b i) (fun b i => later b i) plan).symm

/-- The existing fold extends a typed leaf interpretation as an algebra morphism. -/
def foldHom (H : Family Base Index) (A : Endofunctor.Algebra P.endofunctor)
    (interpret : H ⟶ A.a) : freeAlgebra P H ⟶ A where
  f := fun base index => ↾(Free.fold P (fun b i => interpret b i)
    (pointwiseAlgebra P A) base index)
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro layer
    cases layer
    rfl

/-- Restrict an algebra morphism to its typed hole values. -/
def restrict (H : Family Base Index) (A : Endofunctor.Algebra P.endofunctor)
    (hom : freeAlgebra P H ⟶ A) : H ⟶ A.a :=
  fun base index => ↾(fun hole => hom.f base index (Free.pure P hole))

/-- The universal bijection comes from the original fold uniqueness theorem. -/
def homEquiv (H : Family Base Index) (A : Endofunctor.Algebra P.endofunctor) :
    (freeAlgebra P H ⟶ A) ≃ (H ⟶ A.a) where
  toFun := restrict P H A
  invFun := foldHom P H A
  left_inv hom := by
    apply Endofunctor.Algebra.ext
    funext base index
    apply ConcreteCategory.hom_ext
    intro plan
    exact (Free.fold_unique P (fun b i hole => hom.f b i (Free.pure P hole))
      (pointwiseAlgebra P A) (fun b i => hom.f b i)
      (fun _ _ _ => rfl)
      (fun b i shape children => by
        have law := congrArg (fun mapping => mapping b i ⟨shape, children⟩) hom.h
        exact law.symm) base index plan).symm
  right_inv interpret := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro hole
    rfl

/-- Free plans are left adjoint to forgetting the polynomial algebra action. -/
def adjunction : freeFunctor P ⊣ Endofunctor.Algebra.forget P.endofunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv P
      homEquiv_naturality_left_symm := by
        intro H K A earlier interpret
        apply Endofunctor.Algebra.ext
        funext base index
        apply ConcreteCategory.hom_ext
        intro plan
        exact (Free.fold_bind P (fun b i hole => Free.pure P (earlier b i hole))
          (fun b i => interpret b i) (pointwiseAlgebra P A) plan).symm
      homEquiv_naturality_right := by
        intro H A B hom later
        funext base index
        apply ConcreteCategory.hom_ext
        intro hole
        rfl }

/-- The categorical monad is derived from the proved adjunction. -/
def monad : CategoryTheory.Monad (Family Base Index) :=
  (adjunction P).toMonad

/-- The adjunction-generated unit is the original typed hole insertion. -/
theorem unit_apply (H : Family Base Index) (base : Base) (index : Index base)
    (hole : H base index) :
    (monad P).η.app H base index hole = Free.pure P hole := rfl

/-- The adjunction-generated multiplication is the original hole substitution. -/
theorem multiplication_apply (H : Family Base Index) (base : Base) (index : Index base)
    (plan : P.Free (P.Free H) base index) :
    (monad P).μ.app H base index plan = Free.join P plan := rfl

/-- The counit reconstructs in the supplied algebra, using the existing fold. -/
theorem counit_apply (A : Endofunctor.Algebra P.endofunctor)
    (base : Base) (index : Index base) (plan : P.Free A.a base index) :
    ((adjunction P).counit.app A).f base index plan =
      Free.fold P (fun _ _ value => value) (pointwiseAlgebra P A) base index plan := rfl

/-- The induced monad maps leaves by the original map on free plans. -/
theorem map_apply {H K : Family Base Index} (mapping : H ⟶ K)
    (base : Base) (index : Index base) (plan : P.Free H base index) :
    (monad P).map mapping base index plan =
      Free.map P (fun b i => mapping b i) base index plan := rfl

end
end FreeAdjunction
end Mettapedia.TypeTheory.IndexedPolynomial
