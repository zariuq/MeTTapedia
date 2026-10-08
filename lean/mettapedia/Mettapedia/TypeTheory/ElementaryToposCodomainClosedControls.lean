import Mettapedia.TypeTheory.ElementaryToposDependentProductCoherence
import Mettapedia.CategoryTheory.ElementaryToposObjectUniverseAction
import Mettapedia.CategoryTheory.ElementaryToposDependentClosureControls
import Mettapedia.GSLT.Topos.ElementaryToposGeometricControls
import Mettapedia.GSLT.Topos.PresheafTheoryActionControls
import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete

/-!
# Complete chosen-product and object-size controls

Composition retains a varying finite witness and its complete supplied
argument. Actual pullback base change retains the selected source before
and after dependent evaluation. A commuting non-Cartesian square is
excluded. Object lifting carries a non-full geometric map, a nonidentity
exchange and an actual noninvertible ordinary cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposCodomainClosedControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open ElementaryToposDependentProductCoherence
open ElementaryToposDependentClosureControls

abbrev sets : ElementaryTopos.{1,0} :=
  ElementaryTopos.ofCategory (Type) TypeSubobjectClassifier.classifier

/-- The actual constructed codomain model, at its original set-category carrier. -/
def constructedModel : CodomainClosedComprehension (Type) :=
  ElementaryToposCodomainClosedProfile.closedComprehension sets

variable (model : CodomainClosedComprehension (Type))

def completeValue (input : Source) : DependentResult :=
  ⟨input, ⟨min input.2 input.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

def compositeBody : (Over.pullback (sourceBase ≫ doubled)).obj
    (Over.mk doubled) ⟶ dependentResult :=
  Over.homMk (TypeCat.ofHom fun point =>
    let input := pullback.snd doubled (sourceBase ≫ doubled) point
    (⟨input, ⟨min input.2 input.1,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult)) rfl

def compositePoint (number input : Nat) :
    PUnit ⟶ ((Over.pullback (sourceBase ≫ doubled)).obj (Over.mk doubled)).left :=
  pullback.lift (TypeCat.ofHom fun _ => number)
    (TypeCat.ofHom fun _ => (number, input)) rfl

def stagedFunction : Over.mk doubled ⟶
    (model.dependentProduct sourceBase ⋙
      model.dependentProduct doubled).obj
        dependentResult :=
  CodomainClosedComprehension.abstraction
    model doubled
    (CodomainClosedComprehension.abstraction
    model sourceBase
      ((CanonicalSlicePullback.composition sourceBase doubled).inv.app (Over.mk doubled) ≫
        compositeBody))

theorem complete_composition_beta :
    (Over.pullback (sourceBase ≫ doubled)).map
        (stagedFunction model ≫ (CodomainDependentProductReadouts.compositionComparison model sourceBase doubled).inv.app dependentResult) ≫
      model.evaluation
        (sourceBase ≫ doubled) dependentResult = compositeBody :=
  CodomainDependentProductReadouts.composition_application model sourceBase doubled compositeBody

theorem composition_retains_full_input (number input : Nat) :
    ((Over.pullback (sourceBase ≫ doubled)).map
        (stagedFunction model ≫ (CodomainDependentProductReadouts.compositionComparison model sourceBase doubled).inv.app dependentResult) ≫
      model.evaluation
        (sourceBase ≫ doubled) dependentResult).left
          (compositePoint number input PUnit.unit) =
      (⟨(number, input), ⟨min input number,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult) := by
  rw [complete_composition_beta model]
  have reading := congrArg
    (fun arrow : PUnit ⟶ Source => arrow PUnit.unit)
    (pullback.lift_snd (f := doubled) (g := sourceBase ≫ doubled)
      (TypeCat.ofHom fun _ : PUnit => number)
      (TypeCat.ofHom fun _ : PUnit => (number, input)) (show _ = _ from rfl))
  change pullback.snd doubled (sourceBase ≫ doubled)
    (compositePoint number input PUnit.unit) = (number, input) at reading
  change completeValue (pullback.snd doubled (sourceBase ≫ doubled)
    (compositePoint number input PUnit.unit)) = completeValue (number, input)
  exact congrArg completeValue reading

theorem composition_distinguishes_witnesses (model : CodomainClosedComprehension (Type)) :
    (compositeBody.left (compositePoint 1 0 PUnit.unit)).2.val = 0 ∧
      (compositeBody.left (compositePoint 1 1 PUnit.unit)).2.val = 1 := by
  have first := composition_retains_full_input model 1 0
  have second := composition_retains_full_input model 1 1
  rw [complete_composition_beta model] at first second
  constructor
  · exact congrArg (fun value : DependentResult => value.2.val) first
  · exact congrArg (fun value : DependentResult => value.2.val) second

theorem actualSquare : IsPullback (pullback.fst sourceBase shifted)
    (pullback.snd sourceBase shifted) sourceBase shifted := IsPullback.of_hasPullback _ _

def independentArgument : Over Nat := Over.mk (𝟙 Nat)

def suppliedBaseChangeBody :
    (Over.map shifted ⋙ Over.pullback sourceBase).obj independentArgument ⟶ dependentResult :=
  Over.homMk (TypeCat.ofHom fun point =>
    completeValue (pullback.snd (𝟙 Nat ≫ shifted) sourceBase point)) rfl

def baseChangeBody :
    (Over.pullback (pullback.snd sourceBase shifted) ⋙
      Over.map (pullback.fst sourceBase shifted)).obj independentArgument ⟶ dependentResult :=
  (SliceBeckChevalley.sigmaBaseChange actualSquare.flip).hom.app independentArgument ≫
    suppliedBaseChangeBody

/-- Actual sum base change is kept inside the product abstraction, with
both complete projections determining the dependent source. -/
theorem complete_baseChange_abstraction :
    ((Over.mapPullbackAdj shifted).comp
        (model.dependentAdjunction
          sourceBase)).homEquiv independentArgument dependentResult suppliedBaseChangeBody ≫
      (CodomainDependentProductReadouts.baseChange model actualSquare).hom.app dependentResult =
    ((model.dependentAdjunction
        (pullback.snd sourceBase shifted)).comp
      (Over.mapPullbackAdj (pullback.fst sourceBase shifted))).homEquiv
        independentArgument dependentResult baseChangeBody :=
  CodomainDependentProductReadouts.baseChange_abstraction model actualSquare independentArgument dependentResult suppliedBaseChangeBody

def baseChangeFunction : Over.mk (𝟙 Nat) ⟶
    (Over.pullback (pullback.fst sourceBase shifted) ⋙
      model.dependentProduct
        (pullback.snd sourceBase shifted)).obj dependentResult :=
  ((Over.mapPullbackAdj shifted).comp
      (model.dependentAdjunction
        sourceBase)).homEquiv independentArgument dependentResult suppliedBaseChangeBody ≫
    (CodomainDependentProductReadouts.baseChange model actualSquare).hom.app dependentResult

theorem complete_baseChange_evaluation :
    (Over.pullback (pullback.snd sourceBase shifted) ⋙
      Over.map (pullback.fst sourceBase shifted)).map (baseChangeFunction model) ≫
        ((model.dependentAdjunction
            (pullback.snd sourceBase shifted)).comp
          (Over.mapPullbackAdj (pullback.fst sourceBase shifted))).counit.app dependentResult =
      baseChangeBody :=
  CodomainDependentProductReadouts.baseChange_application model actualSquare independentArgument dependentResult suppliedBaseChangeBody

def sourcePoint (number input : Nat) : PUnit ⟶ pullback sourceBase shifted :=
  pullback.lift (TypeCat.ofHom fun _ => (number + 1, input))
    (TypeCat.ofHom fun _ => number) rfl

def baseChangePoint (number input : Nat) : PUnit ⟶
    pullback (𝟙 Nat) (pullback.snd sourceBase shifted) :=
  pullback.lift (TypeCat.ofHom fun _ => number) (sourcePoint number input)
    ((pullback.lift_snd (f := sourceBase) (g := shifted)
      (TypeCat.ofHom fun _ : PUnit => (number + 1, input))
      (TypeCat.ofHom fun _ : PUnit => number) (show _ = _ from rfl)).symm)

theorem baseChange_retains_source (number input : Nat) :
    pullback.snd (𝟙 Nat ≫ shifted) sourceBase
      (((SliceBeckChevalley.sigmaBaseChange actualSquare.flip).hom.app
        independentArgument).left (baseChangePoint number input PUnit.unit)) =
      (number + 1, input) := by
  have whole := SliceBeckChevalley.sigmaBaseChangeComponent_snd actualSquare.flip
    independentArgument
  have reading := congrArg
    (fun arrow : pullback (𝟙 Nat) (pullback.snd sourceBase shifted) ⟶ Source =>
      arrow (baseChangePoint number input PUnit.unit)) whole
  change pullback.snd (𝟙 Nat ≫ shifted) sourceBase
      (((SliceBeckChevalley.sigmaBaseChange actualSquare.flip).hom.app
        independentArgument).left (baseChangePoint number input PUnit.unit)) =
    pullback.fst sourceBase shifted
      (pullback.snd (𝟙 Nat) (pullback.snd sourceBase shifted)
        (baseChangePoint number input PUnit.unit)) at reading
  rw [reading]
  have later := congrArg (fun arrow : PUnit ⟶ pullback sourceBase shifted => arrow PUnit.unit)
    (pullback.lift_snd (f := 𝟙 Nat) (g := pullback.snd sourceBase shifted)
      (TypeCat.ofHom fun _ : PUnit => number) (sourcePoint number input)
      ((pullback.lift_snd (f := sourceBase) (g := shifted)
        (TypeCat.ofHom fun _ : PUnit => (number + 1, input))
        (TypeCat.ofHom fun _ : PUnit => number) (show _ = _ from rfl)).symm))
  have earlier := congrArg (fun arrow : PUnit ⟶ Source => arrow PUnit.unit)
    (pullback.lift_fst (f := sourceBase) (g := shifted)
      (TypeCat.ofHom fun _ : PUnit => (number + 1, input))
      (TypeCat.ofHom fun _ : PUnit => number) (show _ = _ from rfl))
  exact (congrArg (pullback.fst sourceBase shifted) later).trans earlier

theorem baseChange_retains_dependent_witness (number input : Nat) :
    baseChangeBody.left (baseChangePoint number input PUnit.unit) =
      (⟨(number + 1, input), ⟨min input (number + 1),
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult) := by
  change completeValue (pullback.snd (𝟙 Nat ≫ shifted) sourceBase
    (((SliceBeckChevalley.sigmaBaseChange actualSquare.flip).hom.app
      independentArgument).left (baseChangePoint number input PUnit.unit))) =
      completeValue (number + 1, input)
  exact congrArg completeValue (baseChange_retains_source number input)

/-- The actual dependent-product mate, followed by complete evaluation,
retains the source and the finite dependent witness. -/
theorem product_baseChange_retains_dependent_witness (number input : Nat) :
    ((Over.pullback (pullback.snd sourceBase shifted) ⋙
        Over.map (pullback.fst sourceBase shifted)).map (baseChangeFunction model) ≫
      ((model.dependentAdjunction
          (pullback.snd sourceBase shifted)).comp
        (Over.mapPullbackAdj (pullback.fst sourceBase shifted))).counit.app dependentResult).left
          (baseChangePoint number input PUnit.unit) =
      (⟨(number + 1, input), ⟨min input (number + 1),
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult) := by
  rw [complete_baseChange_evaluation model]
  exact baseChange_retains_dependent_witness number input

def noSource : Empty ⟶ Nat := TypeCat.ofHom Empty.elim
def toUnit : Nat ⟶ PUnit := TypeCat.ofHom fun _ => PUnit.unit

theorem square_commutes : noSource ≫ toUnit = noSource ≫ toUnit := rfl

/-- A matching target pair has no source witness. This square is
commutative but cannot justify the invertible product comparison. -/
theorem square_is_not_cartesian : ¬ IsPullback noSource noSource toUnit toUnit := by
  intro square
  obtain ⟨point, _, _⟩ := Types.exists_of_isPullback square (0 : Nat) (0 : Nat) rfl
  exact Empty.elim point

/-- The original elementary-topos construction instantiates the complete
varying-argument composition calculation. -/
theorem constructed_composition_readout (number input : Nat) :
    ((Over.pullback (sourceBase ≫ doubled)).map
        (stagedFunction constructedModel ≫ (CodomainDependentProductReadouts.compositionComparison constructedModel sourceBase doubled).inv.app dependentResult) ≫
      constructedModel.evaluation
        (sourceBase ≫ doubled) dependentResult).left
          (compositePoint number input PUnit.unit) =
      (⟨(number, input), ⟨min input number,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult) :=
  composition_retains_full_input constructedModel number input

/-- Its actual product mate over the selected Cartesian square retains
both the changed source and the dependent finite witness. -/
theorem constructed_baseChange_readout (number input : Nat) :
    ((Over.pullback (pullback.snd sourceBase shifted) ⋙
        Over.map (pullback.fst sourceBase shifted)).map (baseChangeFunction constructedModel) ≫
      ((constructedModel.dependentAdjunction
          (pullback.snd sourceBase shifted)).comp
        (Over.mapPullbackAdj (pullback.fst sourceBase shifted))).counit.app dependentResult).left
          (baseChangePoint number input PUnit.unit) =
      (⟨(number + 1, input), ⟨min input (number + 1),
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult) :=
  product_baseChange_retains_dependent_witness constructedModel number input

namespace Size

open ElementaryToposObjectUniverseLift
open Mettapedia.GSLT.Topos.ElementaryToposGeometricControls

theorem exchanged_complete_readout :
    ((map exchange).functor.map ((up diagrams).map
      Mettapedia.GSLT.Core.LambdaTheoryClosedControls.shift)).app
        ⟨false⟩ (10 : Nat) = (12 : Nat) := rfl

theorem lifted_diagonal_is_not_full : ¬ (map diagonal).functor.Full := by
  intro full
  let := full
  apply diagonal_not_full
  refine ⟨?_⟩
  intro first second change
  obtain ⟨preimage, reaches⟩ := (map diagonal).functor.map_surjective ((up diagrams).map change)
  exact ⟨(down sets).map preimage,
    congrArg (fun value => (down diagrams).map value) reaches⟩

end Size

namespace Cell

open ElementaryToposObjectUniverseLift
open Mettapedia.GSLT.Topos.PresheafTheoryAction
open Mettapedia.GSLT.Topos.PresheafTheoryActionControls.Reversal

def presheaves : ElementaryTopos.{1,0} := by
  let : HasSubobjectClassifier (Boolᵒᵖ ⥤ Type) :=
    Mettapedia.GSLT.Topos.presheafCategoryHasClassifierConstructive Bool
  exact ElementaryTopos.ofCategory (Boolᵒᵖ ⥤ Type)
    HasSubobjectClassifier.exists_classifier.some

def topRestriction : ElementaryTopos.GeometricHom presheaves presheaves where
  functor := inverseImage topFunctor
  finite := inverseImage_preservesFiniteLimits topFunctor
  leftAdjoint := ⟨rightKan topFunctor, ⟨rightAdjunction topFunctor⟩⟩

def ordinary : topRestriction.functor ⟶
    (ElementaryTopos.GeometricHom.id presheaves).functor := cell grow

/-- The actual ordinary cell has no inverse, already on one represented
presheaf. Raising objects must retain this asymmetry. -/
theorem ordinary_has_no_inverse :
    ¬ Nonempty ((ElementaryTopos.GeometricHom.id presheaves).functor ⟶
      topRestriction.functor) := by
  rintro ⟨inverse⟩
  apply no_unreversed_cell
  exact ⟨inverse.app representedFalse⟩

theorem lifted_ordinary_has_no_inverse :
    ¬ Nonempty ((map (ElementaryTopos.GeometricHom.id presheaves)).functor ⟶
      (map topRestriction).functor) := by
  rintro ⟨inverse⟩
  apply ordinary_has_no_inverse
  refine ⟨{
    app := fun object =>
      (down presheaves).map (inverse.app ((up presheaves).obj object))
    naturality := ?_ }⟩
  intro first second arrow
  exact congrArg (fun value => (down presheaves).map value)
    (inverse.naturality ((up presheaves).map arrow))

theorem lifted_ordinary_retains_complete_component (object : presheaves) :
    (down presheaves).map ((map₂ ordinary).app ((up presheaves).obj object)) =
      ordinary.app object := rfl

end Cell

end Mettapedia.TypeTheory.ElementaryToposCodomainClosedControls
