import Mettapedia.GSLT.Core.LambdaTheoryBicategory
import Mettapedia.CategoryTheory.StrictTwoCosliceEmbedding

/-!
# Structured lambda theories as strict two-categories

The fixed-source construction is the strict coslice of the actual
finite-limit and exponential preserving theory two-category. The varying
source construction is its strict arrow two-category. Their two-cells
are actual natural transformations, with respectively fixed-source
identity restriction and compatible endpoint components.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory

universe u v

namespace LambdaTheory

abbrev StructuredOver (source : LambdaTheory.{u,v}) :=
  StrictTwoCoslice LambdaTheory.{u,v} source

set_option linter.checkUnivs false in
abbrev Structured := StrictTwoArrow LambdaTheory.{u,v}

namespace StructuredOver

variable {base : LambdaTheory.{u,v}} {source target : StructuredOver base}

/-- A structure-preserving two-cell is the supplied natural transformation;
its restriction to the structure is the identity, including endpoint casts. -/
theorem restriction_identity {first second : source ⟶ target} (change : first ⟶ second) :
    HEq (Functor.whiskerLeft source.leg.functor change.hom) (𝟙 target.leg.functor) :=
  change.fixed

/-- Every individual component at a structure-provided object is fixed. -/
theorem restriction_component {first second : source ⟶ target} (change : first ⟶ second)
    (object : base.Obj) :
    HEq (change.hom.app (source.leg.functor.obj object))
      (𝟙 (target.leg.functor.obj object)) :=
  StrictTwoWhiskering.natTrans_app_heq (congrArg LambdaTheoryMap.functor first.comm)
    (congrArg LambdaTheoryMap.functor second.comm) change.fixed object

/-- Forgetting structure retains the exact supplied outgoing theory map. -/
def forget (base : LambdaTheory.{u,v}) : StrictPseudofunctor (StructuredOver base) LambdaTheory :=
  StrictTwoCoslice.forget

/-- The fixed-source theory inclusion is a strict two-functor and retains
exactly the square cells with identity source component. -/
def intoStructured (base : LambdaTheory.{u,v}) :
    StrictPseudofunctor (StructuredOver base) Structured := StrictTwoCoslice.intoArrow

end StructuredOver

namespace Structured

/-- Endpoint transformations must agree after crossing the authored structure. -/
theorem component_square {source target : Structured.{u,v}}
    {first second : source ⟶ target} (change : first ⟶ second) (object : source.source.Obj) :
    HEq (change.right.app (source.arrow.functor.obj object))
      (target.arrow.functor.map (change.left.app object)) :=
  StrictTwoWhiskering.natTrans_app_heq (congrArg LambdaTheoryMap.functor first.comm)
    (congrArg LambdaTheoryMap.functor second.comm) change.compatible object

def domain : StrictPseudofunctor Structured.{u,v} LambdaTheory := StrictTwoArrow.domain
def codomain : StrictPseudofunctor Structured.{u,v} LambdaTheory := StrictTwoArrow.codomain

end Structured
end LambdaTheory
end Mettapedia.GSLT.Core
