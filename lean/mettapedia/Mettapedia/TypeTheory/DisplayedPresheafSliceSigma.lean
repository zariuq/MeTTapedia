import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafSigma

/-!
# Dependent sums through the family--slice equivalence

The existing displayed CwF's dependent sum corresponds to composition of
the two comprehension projections. The comparison reassociates the base,
first dependent value, and second dependent value; none is truncated.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSliceSigma

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSigma

universe u
variable {C : Type u} [Category.{u} C]
variable {P : Face.{u, u, u} C}

/-- Flattening a dependent pair in a total context is just reassociation,
with the same two dependent values. -/
def sigmaTotalEquiv (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) (c : Cᵒᵖ) :
    (totalSpace (sigmaDisplayed A B)).obj c ≃ (totalSpace B).obj c where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reassociation of dependent pairs respects every contextual substitution. -/
def sigmaTotalIso (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    totalSpace (sigmaDisplayed A B) ≅ totalSpace B := by
  refine NatIso.ofComponents (fun c => (sigmaTotalEquiv A B c).toIso) ?_
  intro c d f
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The sum's projection is the composite of the two original projections. -/
theorem sigmaTotalIso_projection (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    (sigmaTotalIso A B).hom ≫ totalProjection B ≫ totalProjection A =
      totalProjection (sigmaDisplayed A B) := by
  ext c x
  rfl

/-- The CwF dependent sum is the actual slice dependent sum under
comprehension, naturally over its original base. -/
def sigmaSliceIso (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    (totalFunctor P).obj (sigmaDisplayed A B) ≅
      (Over.map (totalProjection A)).obj ((totalFunctor (totalSpace A)).obj B) :=
  Over.isoMk (sigmaTotalIso A B) (sigmaTotalIso_projection A B)

end Mettapedia.TypeTheory.DisplayedPresheafSliceSigma
