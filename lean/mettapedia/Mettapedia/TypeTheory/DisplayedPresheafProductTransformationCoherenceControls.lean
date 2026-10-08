import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherence
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls
import Mathlib.CategoryTheory.SingleObj

/-!
# Witness-sensitive mixed-product controls

Successor and reset are actual nonidentity theory transformations. The two
sides of their native mixed-product square retain the changed argument and
result witness. Reset also provides a local function for which no ordinary
application-preserving transport can exist without an added qualification.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherenceControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafSlicePi DisplayedPresheafPi
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation DisplayedPresheafTheoryTransformationCoherence
open DisplayedPresheafLogicalActionCoherence
open DisplayedPresheafProductTransformationCoherence DependentProductNativeComparison
open DisplayedPresheafTheoryCwfControls DisplayedPresheafTheoryCwfTransformationControls
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

def witnessResults : DisplayedFamily (totalSpace witnesses) :=
  (totalProjection witnesses).mapElements ⋙ witnesses

def identitySection (start : base.Elements) :
    DependentSection witnesses (displayedToTotalElements witnesses ⋙ witnessResults) start where
  app _ _ argument := argument
  naturality _ _ _ := rfl

noncomputable def identityFunction (start : base.Elements) :
    (piDisplayed witnesses witnessResults).obj start :=
  ((nativeIso witnesses).inv.app (displayedToTotalElements witnesses ⋙ witnessResults)).app start
    (identitySection start)

theorem identityFunction_readout (start future : base.Elements) (arrow : start ⟶ future)
    (argument : witnesses.obj future) :
    ((((nativeIso witnesses).hom.app (displayedToTotalElements witnesses ⋙ witnessResults)).app start
      (identityFunction start)).app future arrow argument) = argument := by
  have inverse := congrArg (fun operation => operation.app start (identitySection start))
    ((nativeIso witnesses).inv_hom_id_app (displayedToTotalElements witnesses ⋙ witnessResults))
  exact congrArg (fun functionValue :
    DependentSection witnesses (displayedToTotalElements witnesses ⋙ witnessResults) start =>
      functionValue.app future arrow argument) inverse

noncomputable def mixedOutput (change : selectZero ⟶ selectOne) (number : Nat) : Nat :=
  ((((nativeIso (restrictFamily selectOne base witnesses)).hom.app
    (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
      reindexDisplayed (totalEvidenceMap change base witnesses)
        ((codomainFunctor selectZero base witnesses).obj witnessResults))).app (point selectOne)
    ((productArgumentMap change base witnesses witnessResults).app (point selectOne)
      ((productComparison selectZero base witnesses witnessResults).app
        ((baseMap change base).mapElements.obj (point selectOne))
        ((familyMap change base (piDisplayed witnesses witnessResults)).app (point selectOne)
          (identityFunction ((Functor.Elements.precomp selectOne.op base).obj
            (point selectOne))))))).app (point selectOne) (𝟙 (point selectOne)) number)

set_option backward.isDefEq.respectTransparency false in
theorem mixedOutput_value (change : selectZero ⟶ selectOne) (number : Nat) :
    mixedOutput change number =
      (bodyChange change base witnesses witnessResults).app
        ((displayedToTotalElements (restrictFamily selectOne base witnesses)).obj
          ⟨point selectOne, number⟩) number := by
  have square := congrArg (fun operation =>
      (((nativeIso (restrictFamily selectOne base witnesses)).hom.app
        (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
          reindexDisplayed (totalEvidenceMap change base witnesses)
            ((codomainFunctor selectZero base witnesses).obj witnessResults))).app (point selectOne)
        (operation.app (point selectOne)
          (identityFunction ((Functor.Elements.precomp selectOne.op base).obj (point selectOne))))))
    (product_mixed_square change base witnesses witnessResults)
  have readout := congrArg (fun functionValue :
    DependentSection (restrictFamily selectOne base witnesses)
      (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
        reindexDisplayed (totalEvidenceMap change base witnesses)
          ((codomainFunctor selectZero base witnesses).obj witnessResults)) (point selectOne) =>
      functionValue.app (point selectOne) (𝟙 (point selectOne)) number) square
  change ((((nativeIso (restrictFamily selectOne base witnesses)).hom.app
      (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
        reindexDisplayed (totalEvidenceMap change base witnesses)
          ((codomainFunctor selectZero base witnesses).obj witnessResults))).app (point selectOne)
      (((displayedProductFunctor (restrictFamily selectOne base witnesses)).map
        (bodyChange change base witnesses witnessResults)).app (point selectOne)
          ((productComparison selectOne base witnesses witnessResults).app (point selectOne)
            (identityFunction ((Functor.Elements.precomp selectOne.op base).obj (point selectOne)))))).app
      (point selectOne) (𝟙 (point selectOne)) number) = mixedOutput change number at readout
  rw [productBodyMap_readout, productComparison_readout, identityFunction_readout] at readout
  exact readout.symm

theorem mixed_increment_readout (number : Nat) : mixedOutput increment number = Nat.succ number := by
  rw [mixedOutput_value]
  rfl

theorem mixed_reset_readout (number : Nat) : mixedOutput reset number = 1 := by
  rw [mixedOutput_value]
  rfl

theorem nonidentity_mixed_actions_differ : mixedOutput increment 1 ≠ mixedOutput reset 1 := by
  rw [mixed_increment_readout, mixed_reset_readout]
  decide

theorem increment_retains_distinct_arguments : mixedOutput increment 3 ≠ mixedOutput increment 4 := by
  rw [mixed_increment_readout, mixed_increment_readout]
  decide

theorem reset_identifies_arguments : mixedOutput reset 0 = mixedOutput reset 1 := by
  rw [mixed_reset_readout, mixed_reset_readout]

def boolResults : DisplayedFamily (totalSpace witnesses) := (Functor.const _).obj Bool

noncomputable abbrev localFunctions (selection : Callers ⥤ Worlds) :
    DisplayedFamily (selection.op ⋙ base) :=
  piDisplayed (restrictFamily selection base witnesses) ((codomainFunctor selection base witnesses).obj boolResults)

noncomputable def localReadout (selection : Callers ⥤ Worlds)
    (function : (localFunctions selection).obj (point selection))
    (argument : (restrictFamily selection base witnesses).obj (point selection)) : Bool :=
  ((((nativeIso (restrictFamily selection base witnesses)).hom.app
    (displayedToTotalElements (restrictFamily selection base witnesses) ⋙
      (codomainFunctor selection base witnesses).obj boolResults)).app (point selection) function).app
    (point selection) (𝟙 (point selection)) argument)

def zeroTestSection :
    DependentSection (restrictFamily selectOne base witnesses)
      (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
        (codomainFunctor selectOne base witnesses).obj boolResults) (point selectOne) where
  app _ _ number := by
    change Nat at number
    exact decide (number = 0)
  naturality _ _ _ := rfl

noncomputable def zeroTestFunction : (localFunctions selectOne).obj (point selectOne) :=
  ((nativeIso (restrictFamily selectOne base witnesses)).inv.app
    (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
      (codomainFunctor selectOne base witnesses).obj boolResults)).app (point selectOne) zeroTestSection

theorem zeroTestFunction_readout (number : Nat) :
    localReadout selectOne zeroTestFunction number = decide (number = 0) := by
  have inverse := congrArg (fun operation => operation.app (point selectOne) zeroTestSection)
    ((nativeIso (restrictFamily selectOne base witnesses)).inv_hom_id_app
      (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
        (codomainFunctor selectOne base witnesses).obj boolResults))
  exact congrArg (fun functionValue :
    DependentSection (restrictFamily selectOne base witnesses)
      (displayedToTotalElements (restrictFamily selectOne base witnesses) ⋙
        (codomainFunctor selectOne base witnesses).obj boolResults) (point selectOne) =>
      functionValue.app (point selectOne) (𝟙 (point selectOne)) number) inverse

set_option backward.isDefEq.respectTransparency false in
/-- Reset maps zero and one to the same argument. A supplied local function
distinguishes those values, so even a bare function transport preserving
every application is impossible. A natural transport would be stronger. -/
theorem no_unqualified_application_preserving_transport :
    ¬ ∃ transport : (localFunctions selectOne).obj (point selectOne) →
        (localFunctions selectZero).obj (point selectZero),
      ∀ function (number : Nat),
        localReadout selectZero (transport function)
            ((familyMap reset base witnesses).app (point selectOne) number) =
          localReadout selectOne function number := by
  rintro ⟨transport, preserves⟩
  have atZero := preserves zeroTestFunction 0
  have atOne := preserves zeroTestFunction 1
  rw [zeroTestFunction_readout] at atZero atOne
  change localReadout selectZero (transport zeroTestFunction) (1 : Nat) = true at atZero
  change localReadout selectZero (transport zeroTestFunction) (1 : Nat) = false at atOne
  exact Bool.false_ne_true (atOne.symm.trans atZero)

namespace Covered

abbrev ScalarWorlds := SingleObj Nat

def scalarContext : ScalarWorldsᵒᵖ ⥤ Type where
  obj _ := Nat
  map arrow := TypeCat.ofHom (fun number => Nat.mul arrow.unop number)
  map_id _ := by
    ext number
    exact Nat.one_mul number
  map_comp first second := by
    ext number
    change Nat.mul (Nat.mul first.unop second.unop) number =
      Nat.mul second.unop (Nat.mul first.unop number)
    exact (Nat.mul_assoc first.unop second.unop number).trans
      (Nat.mul_left_comm first.unop second.unop number)

def scalarBase : ScalarWorldsᵒᵖ ⥤ Type := (Functor.const _).obj PUnit
def scalarWitnesses : DisplayedFamily scalarBase := CategoryOfElements.π scalarBase ⋙ scalarContext
def scalarResults : DisplayedFamily (totalSpace scalarWitnesses) :=
  (totalProjection scalarWitnesses).mapElements ⋙ scalarWitnesses

def scalarPoint : scalarBase.Elements := ⟨Opposite.op (SingleObj.star Nat), PUnit.unit⟩

/-- Multiplication gives a genuinely nonidentity theory endotransformation. -/
def scale (factor : Nat) : 𝟭 ScalarWorlds ⟶ 𝟭 ScalarWorlds where
  app _ := factor
  naturality _ _ arrow := Nat.mul_comm factor (show Nat from arrow)

noncomputable instance scalarFutureCoverage
    (point : (((𝟭 ScalarWorlds).op ⋙ scalarBase)).Elements) :
    (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (𝟭 ScalarWorlds).op scalarBase) scalarWitnesses point).Initial := by
  let changed := CategoryOfElementsBaseChange.precompElementsEquivalence
    (𝟭 ScalarWorlds).op.asEquivalence scalarBase
  let : (Functor.Elements.precomp (𝟭 ScalarWorlds).op scalarBase).IsEquivalence := by
    change changed.functor.IsEquivalence
    infer_instance
  infer_instance

noncomputable instance scalarComposedFutureCoverage
    (point : ((((𝟭 ScalarWorlds) ⋙ (𝟭 ScalarWorlds)).op ⋙ scalarBase)).Elements) :
    (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp ((𝟭 ScalarWorlds) ⋙ (𝟭 ScalarWorlds)).op scalarBase)
        scalarWitnesses point).Initial := by
  let changed := CategoryOfElementsBaseChange.precompElementsEquivalence
    ((𝟭 ScalarWorlds) ⋙ (𝟭 ScalarWorlds)).op.asEquivalence scalarBase
  let : (Functor.Elements.precomp ((𝟭 ScalarWorlds) ⋙ (𝟭 ScalarWorlds)).op scalarBase).IsEquivalence := by
    change changed.functor.IsEquivalence
    infer_instance
  infer_instance

def raySection (parameter : Nat) :
    DependentSection scalarWitnesses (displayedToTotalElements scalarWitnesses ⋙ scalarResults)
      scalarPoint where
  app _ arrow _ := Nat.mul arrow.val.unop parameter
  naturality later arrow _ := by
    change Nat.mul later.val.unop (Nat.mul arrow.val.unop parameter) =
      Nat.mul (Nat.mul arrow.val.unop later.val.unop) parameter
    exact (Nat.mul_left_comm later.val.unop arrow.val.unop parameter).trans
      (Nat.mul_assoc arrow.val.unop later.val.unop parameter).symm

noncomputable def rayFunction (parameter : Nat) : (piDisplayed scalarWitnesses scalarResults).obj scalarPoint :=
  ((nativeIso scalarWitnesses).inv.app (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app
    scalarPoint (raySection parameter)

theorem rayFunction_readout (parameter : Nat) (future : scalarBase.Elements)
    (arrow : scalarPoint ⟶ future) (argument : scalarWitnesses.obj future) :
    ((((nativeIso scalarWitnesses).hom.app (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app
      scalarPoint (rayFunction parameter)).app future arrow argument) = Nat.mul arrow.val.unop parameter := by
  have inverse := congrArg (fun operation => operation.app scalarPoint (raySection parameter))
    ((nativeIso scalarWitnesses).inv_hom_id_app (displayedToTotalElements scalarWitnesses ⋙ scalarResults))
  exact congrArg (fun functionValue :
    DependentSection scalarWitnesses (displayedToTotalElements scalarWitnesses ⋙ scalarResults) scalarPoint =>
      functionValue.app future arrow argument) inverse

set_option backward.isDefEq.respectTransparency false in
theorem covered_scale_is_actual_action (factor : Nat) :
    coveredProductTotalTransformation (scale factor) scalarBase scalarWitnesses =
      Functor.whiskerLeft (displayedProductFunctor scalarWitnesses)
        (totalTransformation (scale factor) scalarBase) := by
  have comparison : productTotalComparison (𝟭 ScalarWorlds) scalarBase scalarWitnesses =
      𝟙 (nativeProductTotals (𝟭 ScalarWorlds) scalarBase scalarWitnesses) := by
    unfold productTotalComparison
    rw [productMap_identity]
    rfl
  have iso : coveredProductTotalIso (𝟭 ScalarWorlds) scalarBase scalarWitnesses =
      Iso.refl (nativeProductTotals (𝟭 ScalarWorlds) scalarBase scalarWitnesses) := by
    apply Iso.ext
    rw [coveredProductTotalIso_hom, comparison]
    rfl
  unfold coveredProductTotalTransformation
  rw [iso, comparison]
  simp only [Iso.refl_inv, Category.id_comp]
  exact Category.comp_id _

noncomputable def scaleReadout (factor parameter : Nat) : Nat :=
  ((((nativeIso scalarWitnesses).hom.app (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app
    scalarPoint
    (((coveredProductTotalTransformation (scale factor) scalarBase scalarWitnesses).app scalarResults).app
      (Opposite.op (SingleObj.star Nat)) ⟨PUnit.unit, rayFunction parameter⟩).2).app
    scalarPoint (𝟙 scalarPoint) (0 : Nat))

set_option backward.isDefEq.respectTransparency false in
theorem covered_scale_readout (factor parameter : Nat) : scaleReadout factor parameter = factor * parameter := by
  unfold scaleReadout
  rw [covered_scale_is_actual_action]
  change ((((nativeIso scalarWitnesses).hom.app
    (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app scalarPoint
      ((piDisplayed scalarWitnesses scalarResults).map
        (elementArrow (scale factor) scalarBase scalarPoint) (rayFunction parameter))).app
          scalarPoint (𝟙 scalarPoint) (0 : Nat)) = factor * parameter
  have natural := (((nativeIso scalarWitnesses).hom.app
    (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).naturality_apply
      (elementArrow (scale factor) scalarBase scalarPoint) (rayFunction parameter))
  erw [natural]
  change ((((nativeIso scalarWitnesses).hom.app
    (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app scalarPoint
      (rayFunction parameter)).app scalarPoint
        (elementArrow (scale factor) scalarBase scalarPoint ≫ 𝟙 scalarPoint) (0 : Nat)) = _
  exact (rayFunction_readout parameter scalarPoint
    (elementArrow (scale factor) scalarBase scalarPoint ≫ 𝟙 scalarPoint)
      (show scalarWitnesses.obj scalarPoint from (0 : Nat))).trans (by
        have arrow := congrArg (fun arrow : scalarPoint ⟶ scalarPoint =>
          (show Nat from arrow.val.unop))
            (Category.comp_id (elementArrow (scale factor) scalarBase scalarPoint))
        exact (congrArg (fun number => Nat.mul number parameter) arrow).trans (by rfl))

theorem qualified_nonidentity_actions_distinguish : scaleReadout 2 3 ≠ scaleReadout 3 3 := by
  rw [covered_scale_readout, covered_scale_readout]
  decide

theorem qualified_action_retains_function_witnesses : scaleReadout 2 3 ≠ scaleReadout 2 4 := by
  rw [covered_scale_readout, covered_scale_readout]
  decide

theorem qualified_action_composition :
    coveredProductTotalTransformation (scale 2 ≫ scale 3) scalarBase scalarWitnesses =
      coveredProductTotalTransformation (scale 3) scalarBase scalarWitnesses ≫
        coveredProductTotalTransformation (scale 2) scalarBase scalarWitnesses :=
  coveredProductTotalTransformation_composition (scale 2) (scale 3) scalarBase scalarWitnesses

theorem qualified_action_identity :
    coveredProductTotalTransformation (𝟙 (𝟭 ScalarWorlds)) scalarBase scalarWitnesses =
      𝟙 (nativeProductTotals (𝟭 ScalarWorlds) scalarBase scalarWitnesses) :=
  coveredProductTotalTransformation_identity scalarBase scalarWitnesses

theorem qualified_horizontal_action :
    coveredProductTotalTransformation (scale 2 ◫ scale 3) scalarBase scalarWitnesses =
      coveredProductTotalTransformation (Functor.whiskerRight (scale 2) (𝟭 ScalarWorlds))
        scalarBase scalarWitnesses ≫
      coveredProductTotalTransformation (Functor.whiskerLeft (𝟭 ScalarWorlds) (scale 3))
        scalarBase scalarWitnesses :=
  coveredProductTotalTransformation_horizontal (scale 2) (scale 3) scalarBase scalarWitnesses

end Covered

end Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherenceControls
