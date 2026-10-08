import Mettapedia.TypeTheory.PresheafSliceLogicalAction
import Mettapedia.CategoryTheory.CanonicalSlicePullbackCoherence

/-!
# The contravariant logical pseudofunctor of presheaf slices

Each comparison is the canonical isomorphism of the actual chosen
pullbacks. The unit and associative pasting equations therefore concern
the same substitution functors that carry the classifier and exponential
comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafSliceLogicalAction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafSlice
open scoped Bicategory

universe u
variable {C : Type u} [Category.{u} C]

theorem logical_transport {source target : Face.{u, u, u} C}
    {earlier later : source ⟶ target} (same : earlier = later) :
    (eqToHom (congrArg (fun route => substitution route) same) :
      substitution earlier ⟶ substitution later) =
      (CanonicalSlicePullback.transport same).hom := by
  cases same
  rfl

def identityComparison (base : (Face.{u, u, u} C)ᵒᵖ) :
    substitution (𝟙 base.unop) ≅ 𝟙 (sliceTopos base.unop) :=
  CompleteCocompleteTopos.isoOfNatIso (CanonicalSlicePullback.identity base.unop)

def compositionComparison {first middle last : (Face.{u, u, u} C)ᵒᵖ}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    substitution (f ≫ g).unop ≅ substitution f.unop ≫ substitution g.unop :=
  CompleteCocompleteTopos.isoOfNatIso (CanonicalSlicePullback.composition g.unop f.unop)

def slicePseudofunctor :
    LocallyDiscrete (Face.{u, u, u} C)ᵒᵖ ⥤ᵖ CompleteCocompleteTopos.{u, u + 1, u} :=
  LocallyDiscrete.mkPseudofunctor
    (fun base => sliceTopos base.unop)
    (fun route => substitution route.unop)
    identityComparison compositionComparison
    (by
      intro first second third fourth f g h
      have pasting := CanonicalSlicePullback.forward_pentagon h.unop g.unop f.unop
      convert pasting using 1
      · rfl
      · rfl
      · exact (logical_transport (Category.assoc h.unop g.unop f.unop).symm).trans
          (by cases Category.assoc h.unop g.unop f.unop; rfl))
    (by
      intro first second f
      have pasting := CanonicalSlicePullback.right_triangle f.unop
      change _ = (CanonicalSlicePullback.transport (Category.comp_id f.unop)).hom at pasting
      convert pasting using 1
      · rfl
      · rfl
      · exact logical_transport (Category.comp_id f.unop))
    (by
      intro first second f
      have pasting := CanonicalSlicePullback.left_triangle f.unop
      change _ = (CanonicalSlicePullback.transport (Category.id_comp f.unop)).hom at pasting
      convert pasting using 1
      · rfl
      · rfl
      · exact logical_transport (Category.id_comp f.unop))

end Mettapedia.TypeTheory.PresheafSliceLogicalAction
