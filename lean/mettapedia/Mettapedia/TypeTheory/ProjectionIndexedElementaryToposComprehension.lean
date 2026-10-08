import Mettapedia.TypeTheory.ProjectionIndexedCodomainComprehension
import Mettapedia.TypeTheory.ProjectionIndexedGenericKind
import Mettapedia.TypeTheory.ProjectionIndexedMonomorphismBaseChange
import Mettapedia.TypeTheory.ElementaryToposCodomainClosedProfile
import Mettapedia.CategoryTheory.ElementaryToposPredicateDoctrine

/-!
# Projection-indexed closed comprehension in an elementary topos

The independently constructed dependent products supply the operations.
The codomain calculation earns their actual chosen Beck--Chevalley mates.
The classifier is the domain of an actual terminal kind, and generic truth
is classified on that domain through the earned presentation comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedElementaryToposComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory
open Mettapedia.CategoryTheory.PredicateDoctrine
open ProjectionIndexedComprehension

universe u v w

section Codomain

variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]

local instance codomainFibres : HasFibers.{v,max u v} (codomain C).functor :=
  CodomainComprehension.sliceFibres

local instance codomainTerminal : HasTerminal (codomain C).Base :=
  inferInstanceAs (HasTerminal C)

def terminalKind (base : C) : Arrow C := Arrow.mk (terminal.from base)

def terminalKindPresentation (model : CodomainClosedComprehension C)
    {doctrine : IndexedHeyting.{max u v,v,w} C} (generic : GenericPredicate C doctrine) :
    GenericKindPresentation (ProjectionIndexedCodomainComprehension.closed model).toData
      (𝟭 C) generic where
  object := terminalKind generic.object
  baseTerminal := terminalIsTerminal
  domainIso := by
    change generic.object ≅ generic.object
    exact Iso.refl _

theorem terminalKind_domain (base : C) :
    (CodomainFibrationComprehensionProfile.comprehension.display.obj (terminalKind base)).left =
      base := rfl

theorem terminalKind_projection (base : C) :
    ProjectionIndexedComprehension.Comprehension.displayProjection
      CodomainFibrationComprehensionProfile.comprehension (terminalKind base) =
      terminal.from base := ProjectionIndexedCodomainComprehension.projection_eq _

end Codomain

namespace Size
abbrev raised := ElementaryToposObjectUniverseLift.raised
end Size

variable (topos : ElementaryTopos.{u,v})

local instance raisedFibres : HasFibers.{v,max u v} (codomain (Size.raised topos)).functor :=
  CodomainComprehension.sliceFibres

def profile :
    @ProjectionIndexedComprehension.Closed.{max u v,v,max u v,v} (codomain (Size.raised topos))
      CodomainComprehension.sliceFibres :=
  ProjectionIndexedCodomainComprehension.closed
    (ElementaryToposCodomainClosedProfile.closedComprehension (Size.raised topos))

local instance reflectedFibres : HasFibers.{v,max u v} (predicates (Size.raised topos)).functor :=
  ProjectionIndexedMonomorphismComprehension.fibres

/-- The reflected type comprehension is closed along its actual displays. -/
def typeProfile :
    @ProjectionIndexedComprehension.Closed.{max u v,v,max u v,v}
      (predicates (Size.raised topos)) ProjectionIndexedMonomorphismComprehension.fibres :=
  ProjectionIndexedMonomorphismComprehension.closed
    (ElementaryToposCodomainClosedProfile.closedComprehension (Size.raised topos))

/-- The type display is the actual right-composed kind display. -/
theorem typeProfile_display :
    (typeProfile topos).comprehension.display =
      MonoArrowImageAdjunction.comprehension (Size.raised topos) ⋙
        (profile topos).comprehension.display := rfl

def genericKind : GenericKindPresentation (profile topos).toData
    (𝟭 (Size.raised topos))
    (ElementaryToposPredicateDoctrine.ofTopos (Size.raised topos)).generic :=
  terminalKindPresentation
    (ElementaryToposCodomainClosedProfile.closedComprehension (Size.raised topos))
    (ElementaryToposPredicateDoctrine.ofTopos (Size.raised topos)).generic

theorem genericKind_domain :
    ((profile topos).comprehension.display.obj (genericKind topos).object).left =
      (Size.raised topos).classifier.Ω := rfl

theorem genericKind_projection :
    Comprehension.displayProjection (profile topos).comprehension (genericKind topos).object =
      terminal.from (Size.raised topos).classifier.Ω :=
  terminalKind_projection _

theorem genericKind_classifies (base : Size.raised topos)
    (predicate : Subobject base) :
    (ElementaryToposPredicateDoctrine.ofTopos (Size.raised topos)).reindex
        ((GenericKindPresentation.transported (genericKind topos)).characteristic base predicate)
        (GenericKindPresentation.transported (genericKind topos)).truth = predicate :=
  GenericKindPresentation.transported_classifies (genericKind topos) base predicate

theorem genericKind_unique (base : Size.raised topos) (predicate : Subobject base)
    (map : base ⟶ (GenericKindPresentation.transported (genericKind topos)).object)
    (classifies :
      (ElementaryToposPredicateDoctrine.ofTopos (Size.raised topos)).reindex map
        (GenericKindPresentation.transported (genericKind topos)).truth = predicate) :
    map = (GenericKindPresentation.transported (genericKind topos)).characteristic base predicate :=
  GenericKindPresentation.transported_unique (genericKind topos) base predicate map classifies

end Mettapedia.TypeTheory.ProjectionIndexedElementaryToposComprehension
