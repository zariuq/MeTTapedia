import Mettapedia.CategoryTheory.CodomainStrongSum
import Mettapedia.CategoryTheory.CodomainSliceFibres
import Mettapedia.CategoryTheory.CanonicalSliceAdjointComparisons
import Mettapedia.TypeTheory.SliceBeckChevalley
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Closed codomain comprehension from chosen dependent products

Full comprehension, its unit and strong dependent sums are constructed
for the actual codomain fibration. The remaining model data are the
dependent-product functors and their adjunctions to the actual pullback.
Their unit, composition and Beck--Chevalley comparisons are derived here,
with no preservation laws supplied as model fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe u v

structure CodomainClosedComprehension (C : Type u) [Category.{v} C] [HasFiniteLimits C] where
  dependentProduct : {source target : C} → (source ⟶ target) → Over source ⥤ Over target
  dependentAdjunction : ∀ {source target : C} (route : source ⟶ target),
    Over.pullback route ⊣ dependentProduct route

namespace CodomainClosedComprehension

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable (model : CodomainClosedComprehension C)

def comprehension : Arrow C ⥤ Arrow C := CodomainComprehension.comprehension C
def unit : C ⥤ Arrow C := CodomainComprehension.unit C

def codomainUnitAdjunction : Arrow.rightFunc ⊣ unit (C := C) :=
  CodomainComprehension.codomainAdjunction C

def unitDomainAdjunction : unit (C := C) ⊣ Arrow.leftFunc :=
  CodomainComprehension.domainAdjunction C

instance comprehension_full : (comprehension (C := C)).Full :=
  CodomainComprehension.comprehension_full C

instance comprehension_faithful : (comprehension (C := C)).Faithful :=
  CodomainComprehension.comprehension_faithful C

theorem comprehension_cartesian {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsCartesian square.right square] :
    IsPullback ((comprehension (C := C)).map square).left
      ((comprehension (C := C)).obj first).hom ((comprehension (C := C)).obj second).hom
      ((comprehension (C := C)).map square).right :=
  CodomainComprehension.comprehension_preserves_cartesian square

def evaluation {source target : C} (route : source ⟶ target) (object : Over source) :
    (Over.pullback route).obj ((model.dependentProduct route).obj object) ⟶ object :=
  (model.dependentAdjunction route).counit.app object

def abstraction {source target : C} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    argument ⟶ (model.dependentProduct route).obj result :=
  (model.dependentAdjunction route).homEquiv argument result body

theorem beta {source target : C} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (Over.pullback route).map (abstraction model route body) ≫ evaluation model route result = body :=
  ((model.dependentAdjunction route).homEquiv argument result).symm_apply_apply body

theorem eta {source target : C} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (function : argument ⟶ (model.dependentProduct route).obj result) :
    abstraction model route ((Over.pullback route).map function ≫ evaluation model route result) =
      function :=
  ((model.dependentAdjunction route).homEquiv argument result).apply_symm_apply function

theorem abstraction_unique {source target : C} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result)
    (function : argument ⟶ (model.dependentProduct route).obj result)
    (computes : (Over.pullback route).map function ≫ evaluation model route result = body) :
    function = abstraction model route body := by
  rw [← computes, eta]

def productIdentity (base : C) : model.dependentProduct (𝟙 base) ≅ 𝟭 (Over base) :=
  Adjunction.rightAdjointUniq
    ((model.dependentAdjunction (𝟙 base)).ofNatIsoLeft (CanonicalSlicePullback.identity base))
    (Adjunction.id (C := Over base))

def productComposition {first middle last : C} (f : first ⟶ middle) (g : middle ⟶ last) :
    model.dependentProduct (f ≫ g) ≅ model.dependentProduct f ⋙ model.dependentProduct g :=
  Adjunction.rightAdjointUniq
    ((model.dependentAdjunction (f ≫ g)).ofNatIsoLeft (CanonicalSlicePullback.composition f g))
    ((model.dependentAdjunction g).comp (model.dependentAdjunction f))

theorem productComposition_evaluation {first middle last : C}
    (f : first ⟶ middle) (g : middle ⟶ last) (object : Over first) :
    (Over.pullback g ⋙ Over.pullback f).map ((productComposition model f g).hom.app object) ≫
        ((model.dependentAdjunction g).comp (model.dependentAdjunction f)).counit.app object =
      (CanonicalSlicePullback.composition f g).inv.app
        ((model.dependentProduct (f ≫ g)).obj object) ≫ evaluation model (f ≫ g) object := by
  exact Adjunction.rightAdjointUniq_hom_app_counit _ _ object

variable {first second third fourth : C}
variable {top : first ⟶ second} {left : first ⟶ third}
variable {right : second ⟶ fourth} {bottom : third ⟶ fourth}

def productBaseChange (square : IsPullback top left right bottom) :
    model.dependentProduct right ⋙ Over.pullback bottom ≅
      Over.pullback top ⋙ model.dependentProduct left :=
  conjugateIsoEquiv
    ((Over.mapPullbackAdj bottom).comp (model.dependentAdjunction right))
    ((model.dependentAdjunction left).comp (Over.mapPullbackAdj top))
    (SliceBeckChevalley.sigmaBaseChange square.flip)

theorem productBaseChange_evaluation (square : IsPullback top left right bottom)
    (object : Over second) :
    (Over.pullback left ⋙ Over.map top).map ((productBaseChange model square).hom.app object) ≫
        ((model.dependentAdjunction left).comp (Over.mapPullbackAdj top)).counit.app object =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
        ((model.dependentProduct right ⋙ Over.pullback bottom).obj object) ≫
        ((Over.mapPullbackAdj bottom).comp (model.dependentAdjunction right)).counit.app object :=
  conjugateEquiv_counit _ _ (SliceBeckChevalley.sigmaBaseChange square.flip).hom object

theorem productBaseChange_abstraction (square : IsPullback top left right bottom)
    (argument : Over third) (result : Over second)
    (body : (Over.map bottom ⋙ Over.pullback right).obj argument ⟶ result) :
    ((Over.mapPullbackAdj bottom).comp (model.dependentAdjunction right)).homEquiv argument result body ≫
        (productBaseChange model square).hom.app result =
      ((model.dependentAdjunction left).comp (Over.mapPullbackAdj top)).homEquiv argument result
        ((SliceBeckChevalley.sigmaBaseChange square.flip).hom.app argument ≫ body) := by
  let earlier := (Over.mapPullbackAdj bottom).comp (model.dependentAdjunction right)
  let later := (model.dependentAdjunction left).comp (Over.mapPullbackAdj top)
  let comparison := (SliceBeckChevalley.sigmaBaseChange square.flip).hom
  apply (later.homEquiv argument result).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, productBaseChange_evaluation]
  rw [← Category.assoc, comparison.naturality]
  rw [Category.assoc, ← Adjunction.homEquiv_counit]
  exact congrArg (fun arrow => comparison.app argument ≫ arrow)
    ((earlier.homEquiv argument result).symm_apply_apply body)

end CodomainClosedComprehension
end Mettapedia.TypeTheory
