import Mettapedia.CategoryTheory.ElementaryToposSliceExponentialEquiv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Cartesian closure of elementary-topos slices

The right adjoint to each actual slice tensor functor is constructed from
the earned fibrewise hom equivalence. Naturality in every source arrow
uses the actual pullback projections. No slice closedness is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposSliceExponentials

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open ElementaryToposSliceFunctionSpace

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C) {base : C}

attribute [local instance] Over.cartesianMonoidalCategory

def exponentialObject (source target : Over base) : Over base :=
  Over.mk (functionBase classifier source.hom target.hom)

def overCurry {source context target : Over base} (body : source ⊗ context ⟶ target) :
    context ⟶ exponentialObject classifier source target :=
  Over.homMk (transpose classifier source.hom target.hom context.hom body.left body.w)
    (transpose_base classifier source.hom target.hom context.hom body.left body.w)

def overUncurry {source context target : Over base}
    (function : context ⟶ exponentialObject classifier source target) : source ⊗ context ⟶ target :=
  Over.homMk (untranspose classifier source.hom target.hom context.hom function.left function.w)
    (untranspose_base classifier source.hom target.hom context.hom function.left function.w)

theorem overUncurry_overCurry {source context target : Over base} (body : source ⊗ context ⟶ target) :
    overUncurry classifier (overCurry classifier body) = body := by
  apply Over.OverMorphism.ext
  exact untranspose_transpose classifier source.hom target.hom context.hom body.left body.w

theorem overCurry_overUncurry {source context target : Over base}
    (function : context ⟶ exponentialObject classifier source target) :
    overCurry classifier (overUncurry classifier function) = function := by
  apply Over.OverMorphism.ext
  exact transpose_untranspose classifier source.hom target.hom context.hom function.left function.w

def homEquiv (source context target : Over base) :
    (source ⊗ context ⟶ target) ≃ (context ⟶ exponentialObject classifier source target) where
  toFun := overCurry classifier
  invFun := overUncurry classifier
  left_inv := overUncurry_overCurry classifier
  right_inv := overCurry_overUncurry classifier

theorem homEquiv_naturality (source target : Over base) {earlier later : Over base}
    (arrow : earlier ⟶ later) (body : source ⊗ later ⟶ target) :
    homEquiv classifier source earlier target (source ◁ arrow ≫ body) =
      arrow ≫ homEquiv classifier source later target body := by
  apply Over.OverMorphism.ext
  exact transpose_substitution classifier source.hom target.hom earlier.hom later.hom
    arrow.left arrow.w (source ◁ arrow).left
    (Over.whiskerLeft_left_fst arrow) (Over.whiskerLeft_left_snd arrow) body.left body.w

def exponential (source : Over base) : Over base ⥤ Over base :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft source)
    (fun context target => homEquiv classifier source context target)
    (fun _earlier _later target arrow body => homEquiv_naturality classifier source target arrow body)

def exponentialAdjunction (source : Over base) : tensorLeft source ⊣ exponential classifier source :=
  Adjunction.adjunctionOfEquivRight (F := tensorLeft source)
    (fun context target => homEquiv classifier source context target)
    (fun _earlier _later target arrow body => homEquiv_naturality classifier source target arrow body)

@[instance_reducible]
def closed (source : Over base) : Closed source where
  rightAdj := exponential classifier source
  adj := exponentialAdjunction classifier source

/-- Every slice is closed using only the base exponentials and classifier. -/
@[instance_reducible]
def monoidalClosed (base : C) : MonoidalClosed (Over base) where
  closed := closed classifier

set_option backward.isDefEq.respectTransparency false in
theorem exponentialAdjunction_readout (source context target : Over base)
    (body : source ⊗ context ⟶ target) :
    (exponentialAdjunction classifier source).homEquiv context target body =
      overCurry classifier body := by
  simp only [exponentialAdjunction, Adjunction.adjunctionOfEquivRight,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem exponential_map_readout (source : Over base) {first second : Over base}
    (arrow : first ⟶ second) :
    (exponential classifier source).map arrow =
      overCurry classifier (overUncurry classifier (𝟙 (exponentialObject classifier source first)) ≫ arrow) :=
  rfl

end Mettapedia.CategoryTheory.ElementaryToposSliceExponentials
