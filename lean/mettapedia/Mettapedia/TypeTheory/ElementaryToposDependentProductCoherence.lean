import Mettapedia.TypeTheory.ElementaryToposCodomainClosedProfile
import Mettapedia.TypeTheory.CodomainDependentProductReadouts

/-!
# Chosen dependent-product comparisons in elementary topoi

Identity and composition use uniqueness of the independently constructed
right adjoints. Beck--Chevalley is the mate of the actual sum comparison
of a pullback square. The equations retain complete slice bodies and
evaluations; the square must be Cartesian.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposDependentProductCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open ElementaryToposCodomainClosedProfile

universe u v u₁ v₁ u₂ v₂

/-- Right-adjoint uniqueness retains the entire supplied body, rather
than only asserting that the two dependent products are inhabited. -/
theorem rightComparison_abstraction {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {left : C ⥤ D} {first second : D ⥤ C}
    (earlier : left ⊣ first) (later : left ⊣ second)
    {argument : C} {result : D} (body : left.obj argument ⟶ result) :
    earlier.homEquiv argument result body ≫
      (Adjunction.rightAdjointUniq earlier later).hom.app result =
        later.homEquiv argument result body :=
  CodomainDependentProductReadouts.rightComparison_abstraction earlier later body

variable (topos : ElementaryTopos.{u,v})

/-- Comparison with any independently supplied actual slice right
adjoint. The elementary-topos adjoint on the left is earned here. -/
def comparisonTo (other : CodomainClosedComprehension topos)
    {source target : topos} (route : source ⟶ target) :
    (closedComprehension topos).dependentProduct route ≅
      other.dependentProduct route :=
  CodomainDependentProductReadouts.comparisonTo (closedComprehension topos) other route

theorem comparisonTo_evaluation (other : CodomainClosedComprehension topos)
    {source target : topos} (route : source ⟶ target) (result : Over source) :
    (Over.pullback route).map ((comparisonTo topos other route).hom.app result) ≫
        other.evaluation route result =
      (closedComprehension topos).evaluation route result :=
  CodomainDependentProductReadouts.comparisonTo_evaluation
    (closedComprehension topos) other route result

theorem comparisonTo_abstraction (other : CodomainClosedComprehension topos)
    {source target : topos} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    CodomainClosedComprehension.abstraction (closedComprehension topos) route body ≫
        (comparisonTo topos other route).hom.app result = other.abstraction route body :=
  CodomainDependentProductReadouts.comparisonTo_abstraction
    (closedComprehension topos) other route body

/-- Evaluation determines the whole comparison, for arbitrary slice
objects; no chosen inhabitant or decidable fibre is required. -/
theorem comparisonTo_unique (other : CodomainClosedComprehension topos)
    {source target : topos} (route : source ⟶ target)
    (candidate : (closedComprehension topos).dependentProduct route ⟶
      other.dependentProduct route)
    (readout : ∀ result, (Over.pullback route).map (candidate.app result) ≫
      other.evaluation route result = (closedComprehension topos).evaluation route result) :
    candidate = (comparisonTo topos other route).hom :=
  CodomainDependentProductReadouts.comparisonTo_unique
    (closedComprehension topos) other route candidate readout

def identityComparison (base : topos) :
    (closedComprehension topos).dependentProduct (𝟙 base) ≅
      𝟭 (Over base) :=
  CodomainDependentProductReadouts.identityComparison (closedComprehension topos) base

def compositionComparison {first middle last : topos}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (closedComprehension topos).dependentProduct (earlier ≫ later) ≅
      (closedComprehension topos).dependentProduct earlier ⋙
        (closedComprehension topos).dependentProduct later :=
  CodomainDependentProductReadouts.compositionComparison
    (closedComprehension topos) earlier later

theorem identity_evaluation (base : topos) (result : Over base) :
    (identityComparison topos base).hom.app result =
      (CanonicalSlicePullback.identity base).inv.app
          (((closedComprehension topos).dependentProduct (𝟙 base)).obj result) ≫
        (closedComprehension topos).evaluation (𝟙 base) result :=
  CodomainDependentProductReadouts.identity_evaluation
    (closedComprehension topos) base result

theorem identity_abstraction (base : topos) {argument result : Over base}
    (body : (Over.pullback (𝟙 base)).obj argument ⟶ result) :
    CodomainClosedComprehension.abstraction (closedComprehension topos) (𝟙 base) body ≫
        (identityComparison topos base).hom.app result =
      (CanonicalSlicePullback.identity base).inv.app argument ≫ body :=
  CodomainDependentProductReadouts.identity_abstraction
    (closedComprehension topos) base body

theorem composition_evaluation {first middle last : topos}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (result : Over first) :
    (Over.pullback later ⋙ Over.pullback earlier).map
          ((compositionComparison topos earlier later).hom.app result) ≫
        (Over.pullback earlier).map
          ((closedComprehension topos).evaluation later
            (((closedComprehension topos).dependentProduct earlier).obj result)) ≫
        (closedComprehension topos).evaluation earlier result =
      (CanonicalSlicePullback.composition earlier later).inv.app
          (((closedComprehension topos).dependentProduct
            (earlier ≫ later)).obj result) ≫
        (closedComprehension topos).evaluation (earlier ≫ later) result :=
  CodomainDependentProductReadouts.composition_evaluation
    (closedComprehension topos) earlier later result

theorem composition_abstraction {first middle last : topos}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    {argument : Over last} {result : Over first}
    (body : (Over.pullback (earlier ≫ later)).obj argument ⟶ result) :
    CodomainClosedComprehension.abstraction (closedComprehension topos) (earlier ≫ later) body ≫
        (CodomainDependentProductReadouts.compositionComparison
          (closedComprehension topos) earlier later).hom.app result =
      CodomainClosedComprehension.abstraction (closedComprehension topos) later
        (CodomainClosedComprehension.abstraction (closedComprehension topos) earlier
          ((CanonicalSlicePullback.composition earlier later).inv.app argument ≫ body)) :=
  CodomainDependentProductReadouts.composition_abstraction
    (closedComprehension topos) earlier later body

variable {first second third fourth : topos}
variable {top : first ⟶ second} {left : first ⟶ third}
variable {right : second ⟶ fourth} {bottom : third ⟶ fourth}

def baseChange (square : IsPullback top left right bottom) :
    (closedComprehension topos).dependentProduct right ⋙
        Over.pullback bottom ≅
      Over.pullback top ⋙ (closedComprehension topos).dependentProduct left :=
  CodomainDependentProductReadouts.baseChange (closedComprehension topos) square

/-- The mate retains both the actual sum-pullback comparison and the
complete dependent evaluation. Mere commutativity is insufficient. -/
theorem baseChange_evaluation (square : IsPullback top left right bottom)
    (result : Over second) :
    (Over.pullback left ⋙ Over.map top).map ((baseChange topos square).hom.app result) ≫
        (((closedComprehension topos).dependentAdjunction left).comp
          (Over.mapPullbackAdj top)).counit.app result =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
          (((closedComprehension topos).dependentProduct right ⋙
            Over.pullback bottom).obj result) ≫
        ((Over.mapPullbackAdj bottom).comp
          ((closedComprehension topos).dependentAdjunction right)).counit.app result :=
  CodomainDependentProductReadouts.baseChange_evaluation
    (closedComprehension topos) square result

theorem baseChange_abstraction (square : IsPullback top left right bottom)
    (argument : Over third) (result : Over second)
    (body : (Over.map bottom ⋙ Over.pullback right).obj argument ⟶ result) :
    ((Over.mapPullbackAdj bottom).comp
          ((closedComprehension topos).dependentAdjunction right)).homEquiv argument result body ≫
        (baseChange topos square).hom.app result =
      (((closedComprehension topos).dependentAdjunction left).comp
        (Over.mapPullbackAdj top)).homEquiv argument result
        ((SliceBeckChevalley.sigmaBaseChange square.flip).hom.app argument ≫ body) :=
  CodomainDependentProductReadouts.baseChange_abstraction
    (closedComprehension topos) square argument result body

theorem baseChange_unique (square : IsPullback top left right bottom)
    (candidate : (closedComprehension topos).dependentProduct right ⋙
        Over.pullback bottom ⟶
      Over.pullback top ⋙ (closedComprehension topos).dependentProduct left)
    (readout : ∀ result, (Over.pullback left ⋙ Over.map top).map (candidate.app result) ≫
      (((closedComprehension topos).dependentAdjunction left).comp
        (Over.mapPullbackAdj top)).counit.app result =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
          (((closedComprehension topos).dependentProduct right ⋙
            Over.pullback bottom).obj result) ≫
        ((Over.mapPullbackAdj bottom).comp
          ((closedComprehension topos).dependentAdjunction right)).counit.app result) :
    candidate = (baseChange topos square).hom :=
  CodomainDependentProductReadouts.baseChange_unique
    (closedComprehension topos) square candidate readout

end Mettapedia.TypeTheory.ElementaryToposDependentProductCoherence
