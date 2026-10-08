import Mettapedia.TypeTheory.CodomainClosedComprehension
import Mettapedia.TypeTheory.PresheafSlicePseudofunctor
import Mettapedia.TypeTheory.PresheafDependentBaseChange
import Mettapedia.TypeTheory.PresheafCodomainCosmos

/-!
# Closed, cosmic codomain comprehension of presheaves

Every small presheaf map has both dependent adjoints to its actual slice
pullback. Codomain comprehension is full and has the identity-arrow unit,
with codomain on its left and domain on its right. Its sums are strong by
the computation of the actual opcartesian square; its products obey
Beck--Chevalley for every pullback square.

The slices are complete and cocomplete elementary topoi at the same small
diagram bound. Their substitution is the logical pseudofunctor with the
proved unit and pentagon comparisons. The comparison with the dependent
adjunctions is earned by equality of the universal-property and mate
comparisons. This concerns one presheaf category, not a functor on all topoi.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafCodomainFoundation

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity

universe u
variable (C : Type u) [Category.{u} C]

def closedComprehension : CodomainClosedComprehension (Face.{u, u, u} C) where
  dependentProduct := PresheafDependentAdjunction.dependentProduct
  dependentAdjunction := PresheafDependentAdjunction.dependentAdjunction

abbrev Total := Arrow (Face.{u, u, u} C)

def codomain : Total C ⥤ Face.{u, u, u} C := Arrow.rightFunc
def domain : Total C ⥤ Face.{u, u, u} C := Arrow.leftFunc
def unit : Face.{u, u, u} C ⥤ Total C := CodomainComprehension.unit _
def comprehension : Total C ⥤ Arrow (Face.{u, u, u} C) :=
  CodomainComprehension.comprehension _

def codomainUnitAdjunction : codomain C ⊣ unit C :=
  CodomainComprehension.codomainAdjunction _

def unitDomainAdjunction : unit C ⊣ domain C :=
  CodomainComprehension.domainAdjunction _

instance unit_full : (unit C).Full := CodomainComprehension.unit_full _
instance unit_faithful : (unit C).Faithful := CodomainComprehension.unit_faithful _
instance comprehension_full : (comprehension C).Full :=
  CodomainComprehension.comprehension_full _
instance comprehension_faithful : (comprehension C).Faithful :=
  CodomainComprehension.comprehension_faithful _
instance codomain_fibered : (codomain C).IsFibered :=
  CodomainComprehension.codomain_fibered

@[instance_reducible] def sliceFibres : HasFibers (codomain C) :=
  CodomainComprehension.sliceFibres

def fibreEquivalence (base : Face.{u, u, u} C) :
    Over base ≌ Functor.Fiber (codomain C) base :=
  CodomainComprehension.fibreEquivalence base

theorem comprehension_cartesian {first second : Total C} (square : first ⟶ second)
    [(codomain C).IsCartesian square.right square] :
    IsPullback ((comprehension C).map square).left first.hom second.hom
      ((comprehension C).map square).right := by
  let : Arrow.rightFunc.IsCartesian square.right square :=
    inferInstanceAs ((codomain C).IsCartesian square.right square)
  exact CodomainComprehension.comprehension_preserves_cartesian square

theorem cartesian_iff_pullback {first second : Total C} (square : first ⟶ second) :
    (codomain C).IsCartesian square.right square ↔
      IsPullback square.left first.hom second.hom square.right :=
  CodomainComprehension.cartesian_iff_pullback square

variable {C}
variable {source target : Face.{u, u, u} C} (route : source ⟶ target)

def adjointTriple : (Over.map route ⊣ Over.pullback route) ×
    (Over.pullback route ⊣ (closedComprehension C).dependentProduct route) :=
  ⟨Over.mapPullbackAdj route, (closedComprehension C).dependentAdjunction route⟩

instance substitution_preservesLimits : PreservesLimitsOfSize.{u, u} (Over.pullback route) :=
  (Over.mapPullbackAdj route).rightAdjoint_preservesLimits

instance substitution_preservesColimits : PreservesColimitsOfSize.{u, u} (Over.pullback route) :=
  ((closedComprehension C).dependentAdjunction route).leftAdjoint_preservesColimits

def strongSum (object : Over source) : object.left ≅ ((Over.map route).obj object).left :=
  CodomainComprehension.strongSumComparison route object

theorem strongSum_is_canonical (object : Over source) :
    (strongSum route object).hom =
      ((CodomainComprehension.fibreInclusion source).map
        ((Over.mapPullbackAdj route).unit.app object) ≫
        CodomainComprehension.pullbackLift
          ((CodomainComprehension.fibreInclusion target).obj ((Over.map route).obj object))
          route).left := rfl

@[reassoc] theorem strongSum_display (object : Over source) :
    (strongSum route object).hom ≫ ((Over.map route).obj object).hom = object.hom ≫ route :=
  CodomainComprehension.strongSumComparison_display route object

theorem productIdentity_eq_adjoint (base : Face.{u, u, u} C) :
    CodomainClosedComprehension.productIdentity (closedComprehension C) base =
      PresheafDependentAdjunction.dependentProductId base := by
  unfold CodomainClosedComprehension.productIdentity
  rw [CanonicalSlicePullback.identity_eq_adjoint]
  rfl

theorem productComposition_eq_adjoint {first middle last : Face.{u, u, u} C}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    CodomainClosedComprehension.productComposition (closedComprehension C) f g =
      PresheafDependentAdjunction.dependentProductComp f g := by
  unfold CodomainClosedComprehension.productComposition
  rw [CanonicalSlicePullback.composition_eq_adjoint]
  rfl

variable {first second third fourth : Face.{u, u, u} C}
variable {top : first ⟶ second} {left : first ⟶ third}
variable {right : second ⟶ fourth} {bottom : third ⟶ fourth}

def productBaseChange (square : IsPullback top left right bottom) :
    (closedComprehension C).dependentProduct right ⋙ Over.pullback bottom ≅
      Over.pullback top ⋙ (closedComprehension C).dependentProduct left :=
  CodomainClosedComprehension.productBaseChange (closedComprehension C) square

theorem productBaseChange_evaluation (square : IsPullback top left right bottom)
    (object : Over second) :
    (Over.pullback left ⋙ Over.map top).map ((productBaseChange square).hom.app object) ≫
        (((closedComprehension C).dependentAdjunction left).comp
          (Over.mapPullbackAdj top)).counit.app object =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
        (((closedComprehension C).dependentProduct right ⋙ Over.pullback bottom).obj object) ≫
        ((Over.mapPullbackAdj bottom).comp
          ((closedComprehension C).dependentAdjunction right)).counit.app object :=
  CodomainClosedComprehension.productBaseChange_evaluation (closedComprehension C) square object

theorem productBaseChange_abstraction (square : IsPullback top left right bottom)
    (argument : Over third) (result : Over second)
    (body : (Over.map bottom ⋙ Over.pullback right).obj argument ⟶ result) :
    ((Over.mapPullbackAdj bottom).comp ((closedComprehension C).dependentAdjunction right)).homEquiv
        argument result body ≫ (productBaseChange square).hom.app result =
      (((closedComprehension C).dependentAdjunction left).comp (Over.mapPullbackAdj top)).homEquiv
        argument result ((SliceBeckChevalley.sigmaBaseChange square.flip).hom.app argument ≫ body) :=
  CodomainClosedComprehension.productBaseChange_abstraction
    (closedComprehension C) square argument result body

end Mettapedia.TypeTheory.PresheafCodomainFoundation
