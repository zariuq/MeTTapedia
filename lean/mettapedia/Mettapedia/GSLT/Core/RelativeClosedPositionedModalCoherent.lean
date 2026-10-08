import Mettapedia.GSLT.Core.RelativeClosedPositionedModalLocalModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionCoherent
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension

/-!
# Coherent classification of the complete positioned-modal presentation

The target operations and their local finite diagrams are independently
supplied. A candidate weak finite-limit closed interpretation is admitted
by its base comparison, individual fresh-object isomorphisms and complete
images of the original declaration arrows. The added native inverse arrows
are forced by actual preservation and their defining equations.

Constructor reconstruction earns a comparison on every retained raw object
and every equation-class arrow. Only primitive components are imposed on
cells; their complete uniqueness is derived. Canonical admission and the
identity comparison are calibrated by the independent evaluator. No literal
raw-header equality or varying-theory free/forgetful action is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalCoherent

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization
open ProgramReductionTheory RelativeClosedPositionedModalLocalModels

universe k w
variable {source : Theory.{k,k}} {Index : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (model : LocalModel source selected D)
variable (candidate : Object (RelativeClosedPositionedModalPresentation.nativeSignature source selected) ⥤ D)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate model.nativeModel.meanings)

abbrev LocalArrowAdmission := BaseExtension.Coherent.OldArrowImages model.meanings
  (RelativeClosedPositionedModalPresentation.headers source selected) candidate images

variable (admitted : LocalArrowAdmission model candidate images)

include admitted in
theorem all_primitive_images : CoherentExtension.ArrowImages candidate model.nativeModel.meanings images
    (RelativeClosedPositionedModalPresentation.nativeHeaders source selected) :=
  BaseExtension.Coherent.all_arrow_images model.meanings
    (RelativeClosedPositionedModalPresentation.headers source selected) candidate images admitted

def comparison : candidate ≅ model.nativeDiagram :=
  BaseExtension.Coherent.comparison model.meanings model.realized
    (RelativeClosedPositionedModalPresentation.headers source selected) candidate images admitted

abbrev CellAdmission := BaseExtension.Coherent.CellAdmission model.meanings model.realized candidate images

theorem comparison_admitted : CellAdmission model candidate images
    (comparison model candidate images admitted).hom :=
  BaseExtension.Coherent.comparison_admitted model.meanings model.realized
    (RelativeClosedPositionedModalPresentation.headers source selected) candidate images admitted

theorem admitted_cell_unique (cell : candidate ⟶ model.nativeDiagram)
    (localComponents : CellAdmission model candidate images cell) :
    cell = (comparison model candidate images admitted).hom :=
  BaseExtension.Coherent.admitted_cell_unique model.meanings model.realized
    (RelativeClosedPositionedModalPresentation.headers source selected) candidate images admitted cell localComponents

@[instance_reducible] def admittedCellUnique :
    Unique {cell : candidate ⟶ model.nativeDiagram // CellAdmission model candidate images cell} :=
  BaseExtension.Coherent.admittedCellUnique model.meanings model.realized
    (RelativeClosedPositionedModalPresentation.headers source selected) candidate images admitted

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ model.nativeDiagram // CellAdmission model candidate images iso.hom} :=
  BaseExtension.Coherent.admittedIsoUnique model.meanings model.realized
    (RelativeClosedPositionedModalPresentation.headers source selected) candidate images admitted

theorem comparison_base (object : source.closed.Obj) :
    (comparison model candidate images admitted).hom.app
        (baseObject (RelativeClosedPositionedModalPresentation.nativeSignature source selected) object) =
      images.base.hom.app object ≫
        eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object
          model.nativeModel.meanings model.nativeModel.realization object).symm :=
  (comparison_admitted model candidate images admitted).base object

theorem comparison_object (origin : ULift.{k} (ULift.{k} Unit)) :
    (comparison model candidate images admitted).hom.app (namedObject origin) =
      (images.object origin).hom ≫
        eqToHom (CoherentExtension.target_named_object model.nativeModel.meanings
          model.nativeModel.realization origin).symm :=
  (comparison_admitted model candidate images admitted).object origin

def originalComparison :
    (RelativeClosedPositionedModalPresentation.nativeInclusion source selected).functor ⋙ candidate ≅
      model.diagram :=
  Functor.isoWhiskerLeft (RelativeClosedPositionedModalPresentation.nativeInclusion source selected).functor
    (comparison model candidate images admitted) ≪≫ eqToIso model.original_diagram_readback

theorem whole_arrow_square
    {first second : Object (RelativeClosedPositionedModalPresentation.nativeSignature source selected)}
    (arrow : first ⟶ second) :
    candidate.map arrow ≫ (comparison model candidate images admitted).hom.app second =
      (comparison model candidate images admitted).hom.app first ≫ model.nativeDiagram.map arrow :=
  (comparison model candidate images admitted).hom.naturality arrow

section Canonical

instance native_finite : PreservesFiniteLimits model.nativeDiagram :=
  RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    model.nativeModel.meanings model.nativeModel.realization

instance native_closed : MonoidalClosedFunctor model.nativeDiagram :=
  RelativeClosedSyntax.Interpretation.functor_closed
    model.nativeModel.meanings model.nativeModel.realization

def canonicalImages : AtomicPresentation.PrimitiveImages model.nativeDiagram model.nativeModel.meanings :=
  CanonicalExtension.images model.nativeModel.meanings model.nativeModel.realization

theorem canonical_admitted : LocalArrowAdmission model model.nativeDiagram (canonicalImages model) where
  arrow origin :=
    (CanonicalExtension.arrow_images model.nativeModel.meanings model.nativeModel.realization
      (RelativeClosedPositionedModalPresentation.nativeHeaders source selected)).arrow
        (BaseExtension.originalArrows origin)

theorem canonical_identity_admitted : CellAdmission model model.nativeDiagram (canonicalImages model)
    (𝟙 model.nativeDiagram) :=
  CanonicalExtension.identity_admitted model.nativeModel.meanings model.nativeModel.realization

theorem canonical_comparison_refl :
    comparison model model.nativeDiagram (canonicalImages model) (canonical_admitted model) =
      Iso.refl model.nativeDiagram := by
  apply Iso.ext
  exact (admitted_cell_unique model model.nativeDiagram (canonicalImages model) (canonical_admitted model)
    (𝟙 model.nativeDiagram) (canonical_identity_admitted model)).symm

end Canonical

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalCoherent
