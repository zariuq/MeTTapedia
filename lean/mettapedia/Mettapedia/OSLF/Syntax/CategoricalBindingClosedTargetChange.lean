import Mettapedia.OSLF.Syntax.CategoricalBindingTargetChange

/-!
# Closed functors preserve the selected binding function objects

The chosen function objects of a binding model need not be the internal homs
chosen by a closed category. Their universal properties give a canonical
isomorphism to those internal homs. Combining that isomorphism with the
ordinary exponential comparison supplies the uniform preservation required
for target change.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v u'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Exponential

/-- The canonical isomorphism between two selected function objects with the
same domain and codomain. -/
def iso {C T P Q : D} (E : Exponential C T P) (F : Exponential C T Q) : P ≅ Q where
  hom := F.curry E.eval
  inv := E.curry F.eval
  hom_inv_id := by
    apply E.hom_ext
    simp only [uncurry, whiskerLeft_comp, Category.assoc, E.curry_eval,
      F.curry_eval, whiskerLeft_id, Category.id_comp]
  inv_hom_id := by
    apply F.hom_ext
    simp only [uncurry, whiskerLeft_comp, Category.assoc, F.curry_eval,
      E.curry_eval, whiskerLeft_id, Category.id_comp]

/-- The canonical isomorphism preserves evaluation. -/
theorem iso_eval {C T P Q : D} (E : Exponential C T P) (F : Exponential C T Q) :
    (C ◁ (E.iso F).hom) ≫ F.eval = E.eval :=
  F.curry_eval E.eval

variable [MonoidalClosed D]

/-- The function object selected by the closed-category structure. -/
def closed (C T : D) : Exponential C T (C ⟶[D] T) where
  eval := (ihom.ev C).app T
  curry := MonoidalClosed.curry
  curry_eval f := MonoidalClosed.uncurry_curry f
  curry_unique f g h := by
    exact ((MonoidalClosed.curry_eq_iff f g).mpr h.symm)

/-- A selected function object is isomorphic to the closed-category internal
hom, by its evaluation and currying universal properties. -/
def closedIso {C T P : D} (E : Exponential C T P) : P ≅ (C ⟶[D] T) :=
  E.iso (closed C T)

theorem closedIso_eval {C T P : D} (E : Exponential C T P) :
    (C ◁ E.closedIso.hom) ≫ (ihom.ev C).app T = E.eval :=
  E.iso_eval (closed C T)

end Exponential

variable {D' : Type u'} [Category.{v} D'] [CartesianMonoidalCategory D']
variable [MonoidalClosed D] [MonoidalClosed D']
variable (H : D ⥤ D') [PreservesFiniteProducts H] [MonoidalClosedFunctor H]

/-- The mapped selected object is identified with the target internal hom by
mapping the source universal-property isomorphism and then using the closed
functor's exponential comparison. -/
def closedImageIso {C T P : D} (E : Exponential C T P) :
    H.obj P ≅ ((H.obj C) ⟶[D'] H.obj T) :=
  H.mapIso E.closedIso ≪≫ asIso ((expComparison H C).natTrans.app T)

/-- The comparison sends the selected object's mapped evaluation to the
target evaluation, with the explicit product comparison. -/
theorem closedImageIso_eval {C T P : D} (E : Exponential C T P) :
    (H.obj C ◁ (closedImageIso H E).hom) ≫ (ihom.ev (H.obj C)).app (H.obj T) =
      inv (CartesianMonoidalCategory.prodComparison H C P) ≫ H.map E.eval := by
  simp only [closedImageIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    whiskerLeft_comp, Category.assoc]
  rw [expComparison_ev, ← Category.assoc,
    ← prodComparison_inv_natural_whiskerLeft H, Category.assoc,
    ← H.map_comp, E.closedIso_eval]

/-- Every selected source exponential is preserved at every target stage by
a closed functor. The target object is the actual image of the selected
object, rather than a replacement internal hom. -/
def closedImageExponential {C T P : D} (E : Exponential C T P) :
    Exponential (H.obj C) (H.obj T) (H.obj P) :=
  (Exponential.closed (H.obj C) (H.obj T)).transport
    (Iso.refl _) (Iso.refl _) (closedImageIso H E).symm

theorem closedImageExponential_eval {C T P : D} (E : Exponential C T P) :
    (closedImageExponential H E).eval =
      inv (CartesianMonoidalCategory.prodComparison H C P) ≫ H.map E.eval := by
  simp only [closedImageExponential, Exponential.transport, Exponential.closed,
    Iso.refl_hom, Iso.symm_inv, id_tensorHom, Category.comp_id]
  exact closedImageIso_eval H E

/-- The ordinary closed-functor interface supplies uniform preservation of
all selected binding function objects. -/
instance exponentialPreservationOfClosedFunctor : ExponentialPreservation H where
  image := closedImageExponential H
  eval_image := closedImageExponential_eval H

end Mettapedia.OSLF.Binding.CategoricalBindingModel
