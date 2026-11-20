import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunRearrangement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBlockNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentHelperComparisonData

/-!
# A third dependent firing across a canonical helper diamond

The third firing is reindexed twice in either order. Those telescopes are
not asserted literally equal. They are lifts of the same original telescope
over the same base map, so their universal property gives alikeness of the
actual residual firings. Admission of the third firing is therefore preserved
across the diamond, including its natural predicate queries.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

namespace BlockTriple

def iteratedHelpers (first second third : Helpers Γ) : Helpers (pairFrame first second) :=
  (third.reindex first.weaken).reindex (second.reindex first.weaken).weaken

def iteratedLift (first second third : Helpers Γ) : (iteratedHelpers first second third).frame ⟶ third.frame :=
  Helpers.lift (second.reindex first.weaken).weaken (third.reindex first.weaken) ≫
    Helpers.lift first.weaken third

theorem iterated_isLift (first second third : Helpers Γ) :
    IsLift (pairBase first second) third (iteratedHelpers first second third) (iteratedLift first second third) :=
  (isLift_reindex first.weaken third).paste
    (isLift_reindex (second.reindex first.weaken).weaken (third.reindex first.weaken))

theorem exchange_pairBase (first second : Helpers Γ) :
    exchange first second ≫ pairBase second first = pairBase first second := by
  unfold pairBase
  rw [← Category.assoc, exchange_weaken, Helpers.lift_weaken]

end BlockTriple

namespace DependentRun.Diamond

open BlockTriple

variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L}
  {O : Type} [DecidableEq O] {state : State rules O}
  {first second : HelperFiring levels O state}
  {accepted : (helperStep levels O).Admits first} {accepted' : (helperStep levels O).Admits second}
  (diamond : Diamond first second accepted accepted')

def thirdForward (third : HelperFiring levels O state) : HelperFiring levels O diamond.forward.last :=
  helperResidual (helperResidual first accepted second) diamond.afterFirst (helperResidual first accepted third)

def thirdBackward (third : HelperFiring levels O state) : HelperFiring levels O diamond.backward.last :=
  helperResidual (helperResidual second accepted' first) diamond.afterSecond (helperResidual second accepted' third)

def thirdMovedLeg (third : HelperFiring levels O state) :
    ((diamond.thirdForward third).move diamond.close).helpers.frame ⟶ third.helpers.frame :=
  Helpers.lift diamond.close.frame.hom (iteratedHelpers first.helpers second.helpers third.helpers) ≫
    iteratedLift first.helpers second.helpers third.helpers

theorem thirdMovedLift (third : HelperFiring levels O state) :
    IsLift (pairBase second.helpers first.helpers) third.helpers
      ((diamond.thirdForward third).move diamond.close).helpers (diamond.thirdMovedLeg third) := by
  have firstLift := (iterated_isLift first.helpers second.helpers third.helpers).paste
    (isLift_reindex diamond.close.frame.hom (iteratedHelpers first.helpers second.helpers third.helpers))
  have baseSame : diamond.close.frame.hom ≫ pairBase first.helpers second.helpers =
      pairBase second.helpers first.helpers := exchange_pairBase second.helpers first.helpers
  exact baseSame ▸ firstLift

theorem thirdMovedData (third : HelperFiring levels O state) :
    ((diamond.thirdForward third).move diamond.close).data = third.data.move (diamond.thirdMovedLeg third) := by
  let a := Helpers.lift first.helpers.weaken third.helpers
  let b := Helpers.lift (second.helpers.reindex first.helpers.weaken).weaken
    (third.helpers.reindex first.helpers.weaken)
  let c := Helpers.lift diamond.close.frame.hom
    (iteratedHelpers first.helpers second.helpers third.helpers)
  change ((third.data.move a).move b).move c = third.data.move (c ≫ (b ≫ a))
  exact (Natural.move_comp b c (third.data.move a)).trans
    ((Natural.move_comp a (c ≫ b) third.data).trans
      (congrArg (fun map => third.data.move map) (Category.assoc c b a)))

noncomputable def thirdComparisonData (third : HelperFiring levels O state) :
    AlikeData levels O ((diamond.thirdForward third).move diamond.close) (diamond.thirdBackward third) :=
  alikeDataOfLifts (diamond.thirdMovedLift third)
    (iterated_isLift second.helpers first.helpers third.helpers)
    (diamond.thirdMovedData third) (Natural.move_comp _ _ _)

theorem third_comparison_original (third : HelperFiring levels O state) :
    (diamond.thirdComparisonData third).frame.hom ≫ iteratedLift second.helpers first.helpers third.helpers =
      diamond.thirdMovedLeg third :=
  alikeDataOfLifts_original (diamond.thirdMovedLift third)
    (iterated_isLift second.helpers first.helpers third.helpers)
    (diamond.thirdMovedData third) (Natural.move_comp _ _ _)

theorem third_alike (third : HelperFiring levels O state) :
    HelperAlike levels O ((diamond.thirdForward third).move diamond.close) (diamond.thirdBackward third) :=
  ⟨diamond.thirdComparisonData third⟩

theorem third_admits_iff (third : HelperFiring levels O state) :
    (helperStep levels O).Admits (diamond.thirdForward third) ↔
      (helperStep levels O).Admits (diamond.thirdBackward third) :=
  (helper_admits_move diamond.close (diamond.thirdForward third)).symm.trans
    (helper_admits_alike (diamond.third_alike third))

noncomputable def thirdResultIso (third : HelperFiring levels O state)
    (admitted : (helperStep levels O).Admits (diamond.thirdForward third)) :
    PlainIso levels ((helperStep levels O).result (diamond.thirdForward third) admitted)
      ((helperStep levels O).result (diamond.thirdBackward third) ((diamond.third_admits_iff third).mp admitted)) :=
  (helperResultMove diamond.close (diamond.thirdForward third) admitted).trans
    ((diamond.thirdComparisonData third).resultComparison
      ((helper_admits_move diamond.close (diamond.thirdForward third)).mpr admitted)
      ((diamond.third_admits_iff third).mp admitted))

theorem thirdResultIso_original (third : HelperFiring levels O state)
    (admitted : (helperStep levels O).Admits (diamond.thirdForward third)) :
    (diamond.thirdResultIso third admitted).frame.hom ≫
      iteratedLift first.helpers second.helpers third.helpers = iteratedLift second.helpers first.helpers third.helpers := by
  change ((diamond.thirdComparisonData third).frame.inv ≫
    Helpers.lift diamond.close.frame.hom (iteratedHelpers first.helpers second.helpers third.helpers)) ≫ _ = _
  calc
    _ = (diamond.thirdComparisonData third).frame.inv ≫ diamond.thirdMovedLeg third := Category.assoc _ _ _
    _ = (diamond.thirdComparisonData third).frame.inv ≫
        ((diamond.thirdComparisonData third).frame.hom ≫ iteratedLift second.helpers first.helpers third.helpers) :=
      congrArg (fun map => (diamond.thirdComparisonData third).frame.inv ≫ map) (diamond.third_comparison_original third).symm
    _ = iteratedLift second.helpers first.helpers third.helpers :=
      (diamond.thirdComparisonData third).frame.inv_hom_id_assoc
        (iteratedLift second.helpers first.helpers third.helpers)

theorem thirdResultIso_pair (third : HelperFiring levels O state)
    (admitted : (helperStep levels O).Admits (diamond.thirdForward third)) :
    (diamond.thirdResultIso third admitted).frame.hom ≫ (diamond.thirdForward third).helpers.weaken =
      (diamond.thirdBackward third).helpers.weaken ≫ diamond.close.frame.hom := by
  have inverse : (diamond.thirdComparisonData third).frame.inv ≫
      ((diamond.thirdForward third).move diamond.close).helpers.weaken =
        (diamond.thirdBackward third).helpers.weaken := by
    rw [← (diamond.thirdComparisonData third).commutes, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change ((diamond.thirdComparisonData third).frame.inv ≫ Helpers.lift diamond.close.frame.hom
    (diamond.thirdForward third).helpers) ≫ (diamond.thirdForward third).helpers.weaken = _
  calc
    _ = (diamond.thirdComparisonData third).frame.inv ≫
        (Helpers.lift diamond.close.frame.hom (diamond.thirdForward third).helpers ≫
          (diamond.thirdForward third).helpers.weaken) := Category.assoc _ _ _
    _ = (diamond.thirdComparisonData third).frame.inv ≫
        (((diamond.thirdForward third).move diamond.close).helpers.weaken ≫ diamond.close.frame.hom) :=
      congrArg (fun map => (diamond.thirdComparisonData third).frame.inv ≫ map)
        (Helpers.lift_weaken diamond.close.frame.hom (diamond.thirdForward third).helpers)
    _ = ((diamond.thirdComparisonData third).frame.inv ≫
        ((diamond.thirdForward third).move diamond.close).helpers.weaken) ≫ diamond.close.frame.hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun map => map ≫ diamond.close.frame.hom) inverse

end DependentRun.Diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.third_alike
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.third_admits_iff
