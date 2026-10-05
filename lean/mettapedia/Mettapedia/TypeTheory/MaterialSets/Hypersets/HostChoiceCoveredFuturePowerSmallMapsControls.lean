import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceCoveredFuturePowerSmallMaps
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebraControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

/-!
# Infinite material controls for covered-power smallness

Forgetting a Boolean tag on arbitrary bare hypersets has explicitly
enumerated small fibres. Infinitely many stable predicates in its power
fibre agree at the present stage and project to the same cyclic singleton.
Their later tag admission distinguishes the full future predicates.
Original-bound smallness of that power fibre does not shrink the ambient
hyperset carrier or cover its unrestricted full future predicate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceCoveredFuturePowerSmallMapsControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceCoveredFuturePowerSmallMaps
open PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization

abbrev materials := ContextualMaterialCoalgebra.ambient (D := Stagesᵒᵖ)

def tagged : Stagesᵒᵖ ⥤ Type 1 where
  obj point := materials.obj point × Bool
  map arrow := TypeCat.ofHom fun value => (materials.map arrow value.1, value.2)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext (congrArg (fun map => map value.1) (materials.map_id point)) rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext (congrArg (fun map => map value.1) (materials.map_comp first second)) rfl

def forget : NaturalHom tagged materials where
  app _ value := value.1
  naturality _ _ := rfl

def forgetEnumeration (point : Stagesᵒᵖ) (value : materials.obj point) :
    ContextualImageFactorization.Enumeration.{0,1} (Fibre forget point value) where
  Carrier := Bool
  value flag := ⟨(value, flag), rfl⟩
  covered receipt := ⟨receipt.val.2, Subtype.ext (Prod.ext receipt.property.symm rfl)⟩

theorem forget_small : SmallFibres forget := fun point value => ⟨forgetEnumeration point value⟩

theorem power_forget_small : SmallFibres (imageHom forget) :=
  imageHom_small_of_enumerations forget forgetEnumeration

def thresholdPredicate (number : Nat) (point : Stagesᵒᵖ) : Predicate tagged point where
  holds argument := argument.2.1 = HSet.quineAtom ∧
    (argument.2.2 = false ∨ number+1 ≤ stageIndex argument.1.1)
  closed {first second} move available := by
    have valueEq : first.2.1 = second.2.1 := congrArg Prod.fst move.2
    have tagEq : first.2.2 = second.2.2 := congrArg Prod.snd move.2
    refine ⟨valueEq.symm.trans available.1, ?_⟩
    rcases available.2 with oldFalse | later
    · exact Or.inl (tagEq.symm.trans oldFalse)
    · exact Or.inr (later.trans (growthLe move.1.1))

def thresholdEnumeration (number : Nat) (point : Stagesᵒᵖ) :
    CoveredFuturePowerFamilies.Enumeration (thresholdPredicate number point) where
  Carrier future := {flag : Bool // flag = false ∨ number+1 ≤ stageIndex future.1}
  value _ receipt := (HSet.quineAtom, receipt.val)
  covered _ argument := by
    constructor
    · intro available
      exact ⟨⟨argument.2, available.2⟩, Prod.ext available.1.symm rfl⟩
    · rintro ⟨receipt, same⟩
      exact same ▸ (⟨rfl, receipt.property⟩ :
        (thresholdPredicate number point).holds ⟨_, (HSet.quineAtom, receipt.val)⟩)

def thresholdPower (number : Nat) (point : Stagesᵒᵖ) : Power tagged point :=
  ⟨thresholdPredicate number point, ⟨thresholdEnumeration number point⟩⟩

theorem threshold_restrict (number : Nat) {first second : Stagesᵒᵖ} (arrow : first ⟶ second) :
    restrictPower tagged arrow (thresholdPower number first) = thresholdPower number second := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

theorem threshold_image (number : Nat) (point : Stagesᵒᵖ) :
    imagePower forget point (thresholdPower number point) = singletonPower materials point HSet.quineAtom := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨value, same, materialEq, _⟩
    exact materialEq.symm.trans same
  · intro available
    exact ⟨(argument.2, false), rfl, available.symm, Or.inl rfl⟩

theorem threshold_present (number : Nat) (argument : tagged.obj (world 0)) :
    (thresholdPower number (world 0)).val.holds (current tagged (world 0) argument) ↔
      argument.1 = HSet.quineAtom ∧ argument.2 = false := by
  constructor
  · rintro ⟨materialEq, flagEq | impossible⟩
    · exact ⟨materialEq, flagEq⟩
    · exact (Nat.not_succ_le_zero number impossible).elim
  · intro available
    exact ⟨available.1, Or.inl available.2⟩

theorem agree_on_all_present_arguments (first second : Nat) (argument : tagged.obj (world 0)) :
    (thresholdPower first (world 0)).val.holds (current tagged (world 0) argument) ↔
      (thresholdPower second (world 0)).val.holds (current tagged (world 0) argument) :=
  (threshold_present first argument).trans (threshold_present second argument).symm

def advanceTo (number : Nat) : world 0 ⟶ world number := (homOfLE (Nat.zero_le number)).op.op

theorem threshold_future (number : Nat) :
    (thresholdPower number (world 0)).val.holds
      ⟨⟨world (number+1), advanceTo (number+1)⟩, (HSet.quineAtom, true)⟩ :=
  ⟨rfl, Or.inr (Nat.le_refl _)⟩

theorem threshold_le_of_equal (first second : Nat)
    (same : thresholdPower first (world 0) = thresholdPower second (world 0)) : second ≤ first := by
  have available := threshold_future first
  rw [same] at available
  rcases available.2 with impossible | later
  · cases impossible
  · exact Nat.le_of_succ_le_succ later

theorem threshold_injective : Function.Injective (fun number => thresholdPower number (world 0)) := by
  intro first second same
  exact Nat.le_antisymm (threshold_le_of_equal second first same.symm) (threshold_le_of_equal first second same)

def powerFibre (number : Nat) :
    Fibre (imageHom forget) (world 0) (singletonPower materials (world 0) HSet.quineAtom) :=
  ⟨thresholdPower number (world 0), threshold_image number (world 0)⟩

theorem powerFibre_injective : Function.Injective powerFibre := by
  intro first second same
  exact threshold_injective (congrArg Subtype.val same)

theorem infinite_power_fibre_at_original_bound :
    Nonempty (ContextualImageFactorization.Enumeration.{0,1}
      (Fibre (imageHom forget) (world 0) (singletonPower materials (world 0) HSet.quineAtom))) ∧
      Function.Injective powerFibre :=
  ⟨power_forget_small (world 0) _, powerFibre_injective⟩

theorem power_forget_not_injective : ¬ Function.Injective ((imageHom forget).app (world 0)) := by
  intro injective
  have same := injective ((threshold_image 0 (world 0)).trans (threshold_image 1 (world 0)).symm)
  exact Nat.zero_ne_one (threshold_injective same)

theorem current_evaluation_not_injective :
    ¬ Function.Injective (fun value : Power tagged (world 0) =>
      fun argument => value.val.holds (current tagged (world 0) argument)) := by
  intro injective
  have same := injective (funext fun argument => propext (agree_on_all_present_arguments 0 1 argument))
  exact Nat.zero_ne_one (threshold_injective same)

theorem source_is_not_original_small : ¬ Small.{0} (tagged.obj (world 0)) := by
  intro sourceSmall
  have : Small.{0} (HSet.{0} × Bool) := sourceSmall
  apply UniverseSizeObstructions.ambient_not_small
  exact small_of_injective (f := fun value : HSet.{0} => (value, false))
    (fun _ _ same => congrArg Prod.fst same)

theorem small_power_map_does_not_shrink_source :
    SmallFibres forget ∧ SmallFibres (imageHom forget) ∧ ¬ Small.{0} (tagged.obj (world 0)) :=
  ⟨forget_small, power_forget_small, source_is_not_original_small⟩

def fullMaterialPredicate : Predicate materials (world 0) where
  holds _ := True
  closed _ _ := True.intro

/-- The unrestricted predicate is genuinely too large for the admitted
original receipt bound. This does not follow from absence of a selected decoder. -/
theorem full_material_truth_not_covered :
    ¬ Nonempty (CoveredFuturePowerFamilies.Enumeration fullMaterialPredicate) := by
  rintro ⟨enumeration⟩
  have onto : Function.Surjective (enumeration.value ⟨world 0, 𝟙 (world 0)⟩) :=
    fun value => (enumeration.covered _ value).mp True.intro
  exact UniverseSizeObstructions.ambient_not_small (small_of_surjective onto)

def duplicatedEnumeration : CoveredFuturePowerFamilies.Enumeration
    (singletonPower materials (world 0) HSet.quineAtom).val where
  Carrier _ := Bool
  value _ _ := HSet.quineAtom
  covered _ _ := ⟨fun same => ⟨false, same⟩, fun ⟨_, same⟩ => same⟩

theorem duplicate_receipts_saturated (code : ReceiptCode duplicatedEnumeration)
    (future : PowerClassPresheafBaseChange.Future.Objects (world 0)) :
    code.holds ⟨future, false⟩ ↔ code.holds ⟨future, true⟩ :=
  code.saturated future false true rfl

theorem duplicate_receipts_not_independent (code : ReceiptCode duplicatedEnumeration)
    (future : PowerClassPresheafBaseChange.Future.Objects (world 0)) :
    ¬ (code.holds ⟨future, false⟩ ∧ ¬ code.holds ⟨future, true⟩) :=
  fun ⟨left, right⟩ => right ((duplicate_receipts_saturated code future).mp left)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceCoveredFuturePowerSmallMapsControls
