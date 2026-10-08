import Mettapedia.GSLT.Core.RelativeClosedStructuralImageRealization
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalNativeMeaning
import Mettapedia.CategoryTheory.InternalPredicateConstructorImage

/-!
# Native constructor images and actual generated arrow readouts

The native value classifies the complete existential image of the generic
argument predicate. Classifier uniqueness and the quantified parameter
pullback earn its equality with the authored defining expression. The
resulting generated diagram retains the existing modal values. Endpoint
comparisons then read the actual named quotient arrow as a complete native
function, including every supplied argument and future parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageNativeMeaning

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier

universe k w z p
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D]
variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

def constructorOperation {arguments result : D} (constructor : arguments ⟶ result) :
    power doctrine arguments ⟶ power doctrine result :=
  curry (doctrine.generic.characteristic _
    (doctrine.existsAlong (constructor ▷ power doctrine arguments) (family doctrine (𝟙 _))))

theorem constructorOperation_family {arguments result : D} (constructor : arguments ⟶ result) :
    family doctrine (constructorOperation doctrine constructor) =
      doctrine.existsAlong (constructor ▷ power doctrine arguments) (family doctrine (𝟙 _)) := by
  change doctrine.reindex (uncurry (curry (doctrine.generic.characteristic _ _)))
    doctrine.generic.truth = _
  rw [uncurry_curry, doctrine.generic.classifies]

theorem constructorOperation_complete {arguments result : D} (constructor : arguments ⟶ result) :
    constructorOperation doctrine constructor = existsOperation doctrine constructor := by
  apply family_injective doctrine
  exact (constructorOperation_family doctrine constructor).trans (existsOperation_family doctrine constructor).symm

variable [HasFiniteLimits D]
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)
variable (base : source.closed.Obj ⥤ D)

abbrev meaning := RelativeClosedPredicateLogic.NativeMeaning.meaning base doctrine
abbrev modalValues := RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base

def added (origin : Origins) : RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨power doctrine (base.obj (constructors origin).arguments), power doctrine (base.obj source.program),
    constructorOperation doctrine (base.map (constructors origin).term)⟩

omit [HasFiniteLimits D] in
theorem admitted : RelativeClosedStructuralImageRealization.LocalAdmission source constructors base
    (meaning doctrine source base) (added doctrine source constructors base) := by
  intro origin
  exact congrArg (fun arrow =>
    (⟨power doctrine (base.obj (constructors origin).arguments), power doctrine (base.obj source.program), arrow⟩ :
      RelativeClosedSyntax.Interpretation.ArrowValue D))
    (constructorOperation_complete doctrine (base.map (constructors origin).term))

def meanings := RelativeClosedStructuralImageRealization.assignment source base (meaning doctrine source base)
  (modalValues doctrine source selected base) (added doctrine source constructors base)

theorem realized : RelativeClosedSyntax.Interpretation.Realization
    (RelativeClosedStructuralImagePresentation.signature source selected constructors)
    (meanings doctrine source selected constructors base) :=
  RelativeClosedStructuralImageRealization.realized source selected constructors base (meaning doctrine source base)
    (modalValues doctrine source selected base) (added doctrine source constructors base)
    (RelativeClosedPredicateLogic.NativeMeaning.admitted base doctrine)
    (RelativeClosedPositionedModalNativeMeaning.admitted doctrine source selected base)
    (admitted doctrine source constructors base)

def diagram := RelativeClosedSyntax.Interpretation.functor
  (meanings doctrine source selected constructors base) (realized doctrine source selected constructors base)

theorem named_read (origin : Origins) :
    (meanings doctrine source selected constructors base).evaluateArrow
      (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin).code =
        some (added doctrine source constructors base origin) :=
  RelativeClosedStructuralImageRealization.named_read source selected constructors base (meaning doctrine source base)
    (modalValues doctrine source selected base) (added doctrine source constructors base) origin

theorem complete_named_image (origin : Origins) :
    HEq ((diagram doctrine source selected constructors base).map
      (classOf (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin)))
      (added doctrine source constructors base origin).arrow :=
  RelativeClosedSyntax.Interpretation.functor_map_heq (meanings doctrine source selected constructors base)
    (realized doctrine source selected constructors base)
    (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin)
    (added doctrine source constructors base origin).arrow (named_read doctrine source selected constructors base origin)

def rawSource (origin : Origins) :=
  (DefinitionExtension.definingInclusion (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)).object
      (DefinitionExtension.definingDeclaration (RelativeClosedPositionedModalPresentation.signature source selected)
        (RelativeClosedStructuralImagePresentation.declaration source selected constructors) origin).source

def rawTarget (origin : Origins) :=
  (DefinitionExtension.definingInclusion (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)).object
      (DefinitionExtension.definingDeclaration (RelativeClosedPositionedModalPresentation.signature source selected)
        (RelativeClosedStructuralImagePresentation.declaration source selected constructors) origin).target

theorem endpoints_read (origin : Origins) :
    (meanings doctrine source selected constructors base).evaluateObject (rawSource source selected constructors origin).code =
      some (added doctrine source constructors base origin).source ∧
    (meanings doctrine source selected constructors base).evaluateObject (rawTarget source selected constructors origin).code =
      some (added doctrine source constructors base origin).target := by
  obtain ⟨value, first, second, reading⟩ := RelativeClosedSyntax.Interpretation.sound
    (meanings doctrine source selected constructors base) (realized doctrine source selected constructors base)
    (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin).admitted.some
  have same := Option.some.inj (reading.symm.trans (named_read doctrine source selected constructors base origin))
  cases same
  exact ⟨first, second⟩

theorem source_image (origin : Origins) :
    (diagram doctrine source selected constructors base).obj (rawSource source selected constructors origin) =
      (added doctrine source constructors base origin).source :=
  RelativeClosedSyntax.Interpretation.objectValue_unique (meanings doctrine source selected constructors base)
    (realized doctrine source selected constructors base) _ _ (endpoints_read doctrine source selected constructors base origin).1

theorem target_image (origin : Origins) :
    (diagram doctrine source selected constructors base).obj (rawTarget source selected constructors origin) =
      (added doctrine source constructors base origin).target :=
  RelativeClosedSyntax.Interpretation.objectValue_unique (meanings doctrine source selected constructors base)
    (realized doctrine source selected constructors base) _ _ (endpoints_read doctrine source selected constructors base origin).2

def imageAt (origin : Origins) : (added doctrine source constructors base origin).source ⟶
    (added doctrine source constructors base origin).target :=
  eqToHom (source_image doctrine source selected constructors base origin).symm ≫
    (diagram doctrine source selected constructors base).map
      (classOf (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin)) ≫
        eqToHom (target_image doctrine source selected constructors base origin)

private theorem retype_complete {C : Type w} [Category.{z} C] {X Y X' Y' : C}
    (source : X = X') (target : Y = Y') (first : X ⟶ Y) (second : X' ⟶ Y')
    (same : HEq first second) : eqToHom source.symm ≫ first ≫ eqToHom target = second := by
  cases source
  cases target
  cases same
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem imageAt_complete (origin : Origins) :
    imageAt doctrine source selected constructors base origin =
      constructorOperation doctrine (base.map (constructors origin).term) :=
  retype_complete (source_image doctrine source selected constructors base origin)
    (target_image doctrine source selected constructors base origin)
    ((diagram doctrine source selected constructors base).map
      (classOf (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin)))
    (added doctrine source constructors base origin).arrow
    (complete_named_image doctrine source selected constructors base origin)

theorem supplied_read {parameter : D} (origin : Origins)
    (predicate : parameter ⟶ power doctrine (base.obj (constructors origin).arguments)) :
    family doctrine (predicate ≫ imageAt doctrine source selected constructors base origin) =
      doctrine.existsAlong (base.map (constructors origin).term ▷ parameter) (family doctrine predicate) := by
  rw [imageAt_complete, constructorOperation_complete]
  exact exists_supplied doctrine _ predicate

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageNativeMeaning
