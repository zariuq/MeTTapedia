import Mettapedia.GSLT.Core.RelativeClosedPositionedModalNativeMeaning

/-!
# Complete native readouts of actual generated modal arrows

The endpoint comparisons come from the supplied raw name's formation tree
and the independently checked parser value. They transport the actual
quotient functor image to the independently constructed native operator.
Every function argument and parameter is retained by this equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory

universe k w z p
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)
variable (source : Theory.{k,k}) {Index : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (base : source.closed.Obj ⥤ D)

abbrev meanings := RelativeClosedPositionedModalRealization.assignment source base
  (RelativeClosedPositionedModalNativeMeaning.meaning doctrine source base)
  (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base)

def rawSource (origin : Option Index) :=
  (RelativeClosedPositionedModalPresentation.definingInclusion source selected).object
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected origin).source

def rawTarget (origin : Option Index) :=
  (RelativeClosedPositionedModalPresentation.definingInclusion source selected).object
    (RelativeClosedPositionedModalPresentation.definingDeclaration source selected origin).target

theorem endpoints_read (origin : Option Index) :
    (meanings doctrine source selected base).evaluateObject
        (rawSource source selected origin).code =
      some (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).source ∧
    (meanings doctrine source selected base).evaluateObject
        (rawTarget source selected origin).code =
      some (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).target := by
  obtain ⟨value, first, second, reading⟩ :=
    RelativeClosedSyntax.Interpretation.sound (meanings doctrine source selected base)
      (RelativeClosedPositionedModalNativeMeaning.realized doctrine source selected base)
      (RelativeClosedPositionedModalPresentation.namedRaw source selected origin).admitted.some
  have same := Option.some.inj (reading.symm.trans
    (RelativeClosedPositionedModalNativeMeaning.named_read doctrine source selected base origin))
  cases same
  exact ⟨first, second⟩

theorem source_image (origin : Option Index) :
    (RelativeClosedPositionedModalNativeMeaning.diagram doctrine source selected base).obj
      (rawSource source selected origin) =
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).source :=
  RelativeClosedSyntax.Interpretation.objectValue_unique (meanings doctrine source selected base)
    (RelativeClosedPositionedModalNativeMeaning.realized doctrine source selected base) _ _
    (endpoints_read doctrine source selected base origin).1

theorem target_image (origin : Option Index) :
    (RelativeClosedPositionedModalNativeMeaning.diagram doctrine source selected base).obj
      (rawTarget source selected origin) =
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).target :=
  RelativeClosedSyntax.Interpretation.objectValue_unique (meanings doctrine source selected base)
    (RelativeClosedPositionedModalNativeMeaning.realized doctrine source selected base) _ _
    (endpoints_read doctrine source selected base origin).2

def imageAt (origin : Option Index) :
    (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).source ⟶
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).target :=
  eqToHom (source_image doctrine source selected base origin).symm ≫
    (RelativeClosedPositionedModalNativeMeaning.diagram doctrine source selected base).map
      (classOf (RelativeClosedPositionedModalPresentation.namedRaw source selected origin)) ≫
        eqToHom (target_image doctrine source selected base origin)

theorem imageAt_complete (origin : Option Index) :
    imageAt doctrine source selected base origin =
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).arrow := by
  have complete := (conj_eqToHom_iff_heq
    ((RelativeClosedPositionedModalNativeMeaning.diagram doctrine source selected base).map
      (classOf (RelativeClosedPositionedModalPresentation.namedRaw source selected origin)))
    (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base origin).arrow
    (source_image doctrine source selected base origin) (target_image doctrine source selected base origin)).mpr
      (RelativeClosedPositionedModalNativeMeaning.complete_named_image doctrine source selected base origin)
  simp only [imageAt, complete, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem possibility_supplied {parameter : D}
    (input : parameter ⟶ HigherOrderInternalPredicateQuantifier.power doctrine (base.obj source.program)) :
    HigherOrderInternalPredicateObject.family doctrine
        (input ≫ imageAt doctrine source selected base none) =
      doctrine.existsAlong (base.map source.source ▷ parameter)
        (doctrine.reindex (base.map source.target ▷ parameter)
          (HigherOrderInternalPredicateObject.family doctrine input)) := by
  rw [imageAt_complete]
  change HigherOrderInternalPredicateObject.family doctrine
    (input ≫ RelativeClosedPositionedModalNativeMeaning.possibilityOperation doctrine
      (base.map source.source) (base.map source.target)) = _
  rw [← RelativeClosedPositionedModalNativeMeaning.possibilityOperation_complete,
    ← Category.assoc, HigherOrderInternalPredicateQuantifier.exists_supplied,
    HigherOrderInternalPredicateQuantifier.precomposition_supplied]

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalReadout
