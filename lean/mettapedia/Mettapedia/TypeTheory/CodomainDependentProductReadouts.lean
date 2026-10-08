import Mettapedia.TypeTheory.CodomainClosedComprehension

/-!
# Complete readouts of chosen codomain dependent products

Identity and composition use uniqueness of the independently constructed
right adjoints. Beck--Chevalley is the mate of the actual sum comparison
of a pullback square. The equations retain complete slice bodies and
evaluations; the square must be Cartesian.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.CodomainDependentProductReadouts

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe u v u₁ v₁ u₂ v₂

/-- Right-adjoint uniqueness retains the entire supplied body, rather
than only asserting that the two dependent products are inhabited. -/
theorem rightComparison_abstraction {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {left : C ⥤ D} {first second : D ⥤ C}
    (earlier : left ⊣ first) (later : left ⊣ second)
    {argument : C} {result : D} (body : left.obj argument ⟶ result) :
    earlier.homEquiv argument result body ≫
      (Adjunction.rightAdjointUniq earlier later).hom.app result =
        later.homEquiv argument result body := by
  apply (later.homEquiv argument result).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, Adjunction.rightAdjointUniq_hom_app_counit]
  exact (earlier.homEquiv argument result).symm_apply_apply body

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable (model : CodomainClosedComprehension C)

/-- Comparison with any independently supplied actual slice right
adjoint. Both adjoints are genuine supplied adjunctions to the same slice pullback. -/
def comparisonTo (other : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target) :
    model.dependentProduct route ≅
      other.dependentProduct route :=
  Adjunction.rightAdjointUniq
    (model.dependentAdjunction route)
    (other.dependentAdjunction route)

theorem comparisonTo_evaluation (other : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target) (result : Over source) :
    (Over.pullback route).map ((comparisonTo model other route).hom.app result) ≫
        other.evaluation route result =
      model.evaluation route result :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ result

theorem comparisonTo_abstraction (other : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    CodomainClosedComprehension.abstraction model route body ≫
        (comparisonTo model other route).hom.app result = other.abstraction route body :=
  rightComparison_abstraction _ _ body

/-- Evaluation determines the whole comparison, for arbitrary slice
objects; no chosen inhabitant or decidable fibre is required. -/
theorem comparisonTo_unique (other : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target)
    (candidate : model.dependentProduct route ⟶
      other.dependentProduct route)
    (readout : ∀ result, (Over.pullback route).map (candidate.app result) ≫
      other.evaluation route result = model.evaluation route result) :
    candidate = (comparisonTo model other route).hom := by
  apply NatTrans.ext
  funext result
  apply ((other.dependentAdjunction route).homEquiv _ result).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (readout result).trans (comparisonTo_evaluation model other route result).symm

def identityComparison (base : C) :
    model.dependentProduct (𝟙 base) ≅
      𝟭 (Over base) :=
  model.productIdentity base

def compositionComparison {first middle last : C}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    model.dependentProduct (earlier ≫ later) ≅
      model.dependentProduct earlier ⋙
        model.dependentProduct later :=
  model.productComposition earlier later

theorem identity_evaluation (base : C) (result : Over base) :
    (identityComparison model base).hom.app result =
      (CanonicalSlicePullback.identity base).inv.app
          ((model.dependentProduct (𝟙 base)).obj result) ≫
        model.evaluation (𝟙 base) result := by
  have comparison := Adjunction.rightAdjointUniq_hom_app_counit
    ((model.dependentAdjunction (𝟙 base)).ofNatIsoLeft
      (CanonicalSlicePullback.identity base)) (Adjunction.id (C := Over base)) result
  change (identityComparison model base).hom.app result ≫ 𝟙 result =
    (CanonicalSlicePullback.identity base).inv.app
      ((model.dependentProduct (𝟙 base)).obj result) ≫
        model.evaluation (𝟙 base) result at comparison
  exact (Category.comp_id _).symm.trans comparison

theorem identity_abstraction (base : C) {argument result : Over base}
    (body : (Over.pullback (𝟙 base)).obj argument ⟶ result) :
    CodomainClosedComprehension.abstraction model (𝟙 base) body ≫
        (identityComparison model base).hom.app result =
      (CanonicalSlicePullback.identity base).inv.app argument ≫ body := by
  have comparison := rightComparison_abstraction
    ((model.dependentAdjunction (𝟙 base)).ofNatIsoLeft
      (CanonicalSlicePullback.identity base)) (Adjunction.id (C := Over base))
    ((CanonicalSlicePullback.identity base).inv.app argument ≫ body)
  have identityRead : (Adjunction.id (C := Over base)).homEquiv argument result
      ((CanonicalSlicePullback.identity base).inv.app argument ≫ body) =
        (CanonicalSlicePullback.identity base).inv.app argument ≫ body := by
    change 𝟙 argument ≫ ((CanonicalSlicePullback.identity base).inv.app argument ≫ body) = _
    exact Category.id_comp _
  rw [identityRead] at comparison
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply] at comparison
  simp only [Iso.hom_inv_id_app_assoc,
    CodomainClosedComprehension.abstraction,
    identityComparison, CodomainClosedComprehension.productIdentity] at comparison ⊢
  exact comparison

theorem composition_evaluation {first middle last : C}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (result : Over first) :
    (Over.pullback later ⋙ Over.pullback earlier).map
          ((compositionComparison model earlier later).hom.app result) ≫
        (Over.pullback earlier).map
          (model.evaluation later
            ((model.dependentProduct earlier).obj result)) ≫
        model.evaluation earlier result =
      (CanonicalSlicePullback.composition earlier later).inv.app
          ((model.dependentProduct
            (earlier ≫ later)).obj result) ≫
        model.evaluation (earlier ≫ later) result := by
  have comparison :=
    model.productComposition_evaluation earlier later result
  rw [Adjunction.comp_counit_app] at comparison
  change (Over.pullback later ⋙ Over.pullback earlier).map
      ((compositionComparison model earlier later).hom.app result) ≫
      ((Over.pullback earlier).map
        (model.evaluation later
          ((model.dependentProduct earlier).obj result)) ≫
        model.evaluation earlier result) = _ at comparison
  exact comparison

theorem composition_abstraction {first middle last : C}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    {argument : Over last} {result : Over first}
    (body : (Over.pullback (earlier ≫ later)).obj argument ⟶ result) :
    CodomainClosedComprehension.abstraction model (earlier ≫ later) body ≫
        (compositionComparison model earlier later).hom.app result =
      CodomainClosedComprehension.abstraction model later
        (CodomainClosedComprehension.abstraction model earlier
          ((CanonicalSlicePullback.composition earlier later).inv.app argument ≫ body)) := by
  have comparison := rightComparison_abstraction
    ((model.dependentAdjunction (earlier ≫ later)).ofNatIsoLeft
      (CanonicalSlicePullback.composition earlier later))
    ((model.dependentAdjunction later).comp
      (model.dependentAdjunction earlier))
    ((CanonicalSlicePullback.composition earlier later).inv.app argument ≫ body)
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv] at comparison
  simp only [Iso.hom_inv_id_app_assoc,
    CodomainClosedComprehension.abstraction,
    compositionComparison, CodomainClosedComprehension.productComposition] at comparison ⊢
  exact comparison

theorem composition_application {first middle last : C}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    {argument : Over last} {result : Over first}
    (body : (Over.pullback (earlier ≫ later)).obj argument ⟶ result) :
    (Over.pullback (earlier ≫ later)).map
        (model.abstraction later
          (model.abstraction earlier
            ((CanonicalSlicePullback.composition earlier later).inv.app argument ≫ body)) ≫
          (compositionComparison model earlier later).inv.app result) ≫
        model.evaluation (earlier ≫ later) result = body := by
  rw [← composition_abstraction model earlier later body]
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact model.beta (earlier ≫ later) body

variable {first second third fourth : C}
variable {top : first ⟶ second} {left : first ⟶ third}
variable {right : second ⟶ fourth} {bottom : third ⟶ fourth}

def baseChange (square : IsPullback top left right bottom) :
    model.dependentProduct right ⋙
        Over.pullback bottom ≅
      Over.pullback top ⋙ model.dependentProduct left :=
  model.productBaseChange square

/-- The mate retains both the actual sum-pullback comparison and the
complete dependent evaluation. Mere commutativity is insufficient. -/
theorem baseChange_evaluation (square : IsPullback top left right bottom)
    (result : Over second) :
    (Over.pullback left ⋙ Over.map top).map ((baseChange model square).hom.app result) ≫
        ((model.dependentAdjunction left).comp
          (Over.mapPullbackAdj top)).counit.app result =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
          ((model.dependentProduct right ⋙
            Over.pullback bottom).obj result) ≫
        ((Over.mapPullbackAdj bottom).comp
          (model.dependentAdjunction right)).counit.app result :=
  model.productBaseChange_evaluation square result

theorem baseChange_abstraction (square : IsPullback top left right bottom)
    (argument : Over third) (result : Over second)
    (body : (Over.map bottom ⋙ Over.pullback right).obj argument ⟶ result) :
    ((Over.mapPullbackAdj bottom).comp
          (model.dependentAdjunction right)).homEquiv argument result body ≫
        (baseChange model square).hom.app result =
      ((model.dependentAdjunction left).comp
        (Over.mapPullbackAdj top)).homEquiv argument result
        ((SliceBeckChevalley.sigmaBaseChange square.flip).hom.app argument ≫ body) :=
  model.productBaseChange_abstraction square argument result body

theorem baseChange_application (square : IsPullback top left right bottom)
    (argument : Over third) (result : Over second)
    (body : (Over.map bottom ⋙ Over.pullback right).obj argument ⟶ result) :
    (Over.pullback left ⋙ Over.map top).map
        (((Over.mapPullbackAdj bottom).comp
          (model.dependentAdjunction right)).homEquiv argument result body ≫
          (baseChange model square).hom.app result) ≫
        ((model.dependentAdjunction left).comp
          (Over.mapPullbackAdj top)).counit.app result =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app argument ≫ body := by
  change (((model.dependentAdjunction left).comp
    (Over.mapPullbackAdj top)).homEquiv argument result).symm _ = _
  rw [baseChange_abstraction model square argument result body]
  exact Equiv.symm_apply_apply _ _

theorem baseChange_unique (square : IsPullback top left right bottom)
    (candidate : model.dependentProduct right ⋙
        Over.pullback bottom ⟶
      Over.pullback top ⋙ model.dependentProduct left)
    (readout : ∀ result, (Over.pullback left ⋙ Over.map top).map (candidate.app result) ≫
      ((model.dependentAdjunction left).comp
        (Over.mapPullbackAdj top)).counit.app result =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
          ((model.dependentProduct right ⋙
            Over.pullback bottom).obj result) ≫
        ((Over.mapPullbackAdj bottom).comp
          (model.dependentAdjunction right)).counit.app result) :
    candidate = (baseChange model square).hom := by
  apply NatTrans.ext
  funext result
  apply (((model.dependentAdjunction left).comp
    (Over.mapPullbackAdj top)).homEquiv _ result).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (readout result).trans (baseChange_evaluation model square result).symm

end Mettapedia.TypeTheory.CodomainDependentProductReadouts
