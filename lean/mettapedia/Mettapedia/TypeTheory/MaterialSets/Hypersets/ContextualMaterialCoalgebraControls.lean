import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeOperations
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent

/-!
# Material membership readout and contextual finality controls

An actual graph containing the empty and cyclic values supplies a small
presented source coalgebra. Its constructed decoder gives a denotation-
preserving natural readout satisfying the complete membership-image law.

On the infinite advancing stage site, a small-covered predicate admits
only the empty hyperset after stage zero. No fixed material membership
predicate equals it. An actual coalgebra adding such a late-only node has
no morphism into constant material membership. Thus this constant ambient
coalgebra is not a weakly final contextual coalgebra.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebraControls

open _root_.CategoryTheory PowerClassPresheafBaseChange
open PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover

abbrev materials := ContextualMaterialCoalgebra.ambient (D := Stagesᵒᵖ)
abbrev membership := ContextualMaterialCoalgebra.coalgebra (D := Stagesᵒᵖ)

def laterOnly (point : Stagesᵒᵖ) : CoveredFuturePowerFamilies.Predicate materials point where
  holds argument := 1 ≤ stageIndex argument.1.1 ∧ argument.2 = (∅ : HSet.{0})
  closed {first second} move available := by
    have same : (first.2 : HSet.{0}) = second.2 := move.2
    exact ⟨available.1.trans (growthLe move.1.1), same.symm.trans available.2⟩

def laterEnumeration (point : Stagesᵒᵖ) : CoveredFuturePowerFamilies.Enumeration (laterOnly point) where
  Carrier future := {receipt : PUnit.{1} // 1 ≤ stageIndex future.1}
  value _ _ := (∅ : HSet.{0})
  covered _ argument := by
    constructor
    · rintro ⟨later, same⟩
      exact ⟨⟨PUnit.unit, later⟩, same.symm⟩
    · rintro ⟨receipt, same⟩
      exact ⟨receipt.property, same.symm⟩

def laterPower (point : Stagesᵒᵖ) : CoveredFuturePowerFamilies.Power materials point :=
  ⟨laterOnly point, ⟨laterEnumeration point⟩⟩

theorem laterPower_natural {first second : Stagesᵒᵖ} (step : first ⟶ second) :
    CoveredFuturePowerFamilies.restrictPower materials step (laterPower first) = laterPower second := by
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro _
  exact Iff.rfl

def laterSection : (CoveredFuturePowerFamilies.family materials).sections :=
  ⟨laterPower, fun step => laterPower_natural step⟩

def firstAdvance : world 0 ⟶ world 1 := (homOfLE (Nat.zero_le 1)).op.op

theorem later_empty_admitted :
    (laterPower (world 0)).val.holds ⟨⟨world 1, firstAdvance⟩, (∅ : HSet)⟩ :=
  ⟨Nat.le_refl 1, rfl⟩

theorem no_present_admitted (argument : HSet) :
    ¬ (laterPower (world 0)).val.holds (CoveredFuturePowerFamilies.current materials (world 0) argument) :=
  fun available => Nat.not_succ_le_zero 0 available.1

/-- This covered natural predicate cannot be the membership of any fixed
material set, because the same empty value is absent now and present later. -/
theorem laterPower_not_membership_image :
    ¬ ∃ value : HSet, membership.app (world 0) value = laterPower (world 0) := by
  rintro ⟨value, same⟩
  have later := later_empty_admitted
  rw [← same] at later
  have present : (membership.app (world 0) value).val.holds
      (CoveredFuturePowerFamilies.current materials (world 0) (∅ : HSet)) := later
  rw [same] at present
  exact no_present_admitted ∅ present

theorem membership_not_surjective : ¬ Function.Surjective (membership.app (world 0)) :=
  fun onto => laterPower_not_membership_image (onto (laterPower (world 0)))

namespace LateNode

def states : Stagesᵒᵖ ⥤ Type 1 where
  obj _ := Option HSet
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def embedding : NaturalHom materials states where
  app _ := some
  naturality _ _ := rfl

def coalgebra : NaturalHom states (CoveredFuturePowerFamilies.family states) where
  app point state := match state with
    | none => CoveredFuturePowerFunctor.imagePower embedding point (laterPower point)
    | some value => CoveredFuturePowerFunctor.imagePower embedding point (membership.app point value)
  naturality {first second} step state := by
    cases state with
    | none =>
      exact (CoveredFuturePowerFunctor.imagePower_restrict embedding step (laterPower first)).trans
        (congrArg (CoveredFuturePowerFunctor.imagePower embedding second) (laterPower_natural step))
    | some value =>
      exact (CoveredFuturePowerFunctor.imagePower_restrict embedding step (membership.app first value)).trans
        (congrArg (CoveredFuturePowerFunctor.imagePower embedding second) (membership.naturality step value))

theorem lateNode_no_present_children (child : states.obj (world 0)) :
    ¬ (coalgebra.app (world 0) none).val.holds
      (CoveredFuturePowerFamilies.current states (world 0) child) := by
  rintro ⟨value, _same, available⟩
  exact no_present_admitted value available

theorem lateNode_empty_future :
    (coalgebra.app (world 0) none).val.holds ⟨⟨world 1, firstAdvance⟩, some (∅ : HSet)⟩ :=
  ⟨(∅ : HSet.{0}), rfl, later_empty_admitted⟩

/-- This is an actual small-covered contextual coalgebra without a map
into constant membership, not only a failed inverse of its structure map. -/
theorem no_material_coalgebra_morphism :
    ¬ ∃ reading : NaturalHom states materials,
      coalgebra.comp (CoveredFuturePowerFunctor.imageHom reading) = reading.comp membership := by
  rintro ⟨reading, square⟩
  have empty : reading.app (world 0) none = (∅ : HSet) := by
    apply HSet.eq_empty_iff.mpr
    intro value available
    obtain ⟨child, _same, childStep⟩ :=
      (ContextualMaterialCoalgebra.coalgebra_readout_iff coalgebra reading).mp square
        (world 0) none ⟨world 0, 𝟙 (world 0)⟩ value |>.mp available
    exact lateNode_no_present_children child childStep
  have available : HSet.Mem (reading.app (world 0) none)
      (reading.app (world 1) (some (∅ : HSet))) :=
    ((ContextualMaterialCoalgebra.coalgebra_readout_iff coalgebra reading).mp square
      (world 0) none ⟨world 1, firstAdvance⟩ _).mpr
        ⟨some ∅, rfl, lateNode_empty_future⟩
  rw [empty] at available
  exact HSet.notMem_empty _ available

end LateNode

namespace Presented

open AccessiblePointedGraph

def graph : AccessiblePointedGraph :=
  sup fun tag : Bool => if tag then HSet.loop else AccessiblePointedGraph.empty

def graphMembers : {value : HSet // value ∈ HSet.mk graph} ≃ PicturedMembers graph where
  toFun member := ⟨member.val, by rw [picture_eq_mk]; exact member.property⟩
  invFun member := ⟨member.val, by rw [← picture_eq_mk]; exact member.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def model : PresentedType (PowerMemberClass graph) where
  graph := graph
  decode := graphMembers.trans (powerMemberEquiv graph).symm

def states : Stagesᵒᵖ ⥤ Type where
  obj _ := PowerMemberClass graph
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def reading : NaturalHom states materials := ContextualMaterialCoalgebra.readout
  (fun _ value => model.value value) (fun _ _ => rfl)

def children (point : Stagesᵒᵖ) (value : states.obj point) :
    CoveredFuturePowerFamilies.Predicate states point where
  holds argument := model.value argument.2 ∈ model.value value
  closed {_ _} move available := move.2 ▸ available

def coalgebra : NaturalHom states (CoveredFuturePowerFamilies.family states) where
  app point value := ⟨children point value, ⟨CoveredFuturePowerFamilies.smallEnumeration (children point value)⟩⟩
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

theorem empty_mem_carrier : (∅ : HSet) ∈ model.carrier :=
  HSet.mem_range.mpr ⟨false, HSet.mk_empty⟩

theorem quine_mem_carrier : HSet.quineAtom ∈ model.carrier :=
  HSet.mem_range.mpr ⟨true, HSet.mk_loop⟩

theorem carrier_members_closed {parent child : HSet}
    (available : parent ∈ model.carrier) (member : child ∈ parent) : child ∈ model.carrier := by
  obtain ⟨tag, same⟩ := HSet.mem_range.mp available
  cases tag with
  | false =>
    have empty : parent = (∅ : HSet) := same.symm.trans HSet.mk_empty
    rw [empty] at member
    exact (HSet.notMem_empty _ member).elim
  | true =>
    have cyclic : parent = HSet.quineAtom := same.symm.trans HSet.mk_loop
    rw [cyclic] at member
    exact HSet.mem_quineAtom.mp member ▸ quine_mem_carrier

theorem exact_readout_square :
    coalgebra.comp (CoveredFuturePowerFunctor.imageHom reading) = reading.comp membership := by
  apply (ContextualMaterialCoalgebra.coalgebra_readout_iff coalgebra reading).mpr
  intro point argument future value
  constructor
  · intro member
    let child := model.decode ⟨value, carrier_members_closed (model.value_mem argument) member⟩
    have same : model.value child = value := model.value_decode _
    have childStep : model.value child ∈ model.value argument := same.symm ▸ member
    exact ⟨child, same, childStep⟩
  · rintro ⟨child, same, member⟩
    change model.value child = value at same
    change model.value child ∈ model.value argument at member
    exact same ▸ member

def emptyValue : states.obj (world 0) := model.decode ⟨∅, empty_mem_carrier⟩
def cyclicValue : states.obj (world 0) := model.decode ⟨HSet.quineAtom, quine_mem_carrier⟩

theorem emptyValue_readout : reading.app (world 0) emptyValue = (∅ : HSet) := model.value_decode _

theorem cyclicValue_readout : reading.app (world 0) cyclicValue = HSet.quineAtom := model.value_decode _

theorem cyclic_self_child :
    (coalgebra.app (world 0) cyclicValue).val.holds
      (CoveredFuturePowerFamilies.current states (world 0) cyclicValue) := by
  change model.value cyclicValue ∈ model.value cyclicValue
  have same : model.value cyclicValue = HSet.quineAtom := cyclicValue_readout
  exact Eq.mpr (congrArg (fun value : HSet => value ∈ value) same) HSet.quineAtom_mem_self

theorem empty_cyclic_classes_differ :
    (ContextualCoalgebraQuotient.projection coalgebra).app (world 0) emptyValue ≠
      (ContextualCoalgebraQuotient.projection coalgebra).app (world 0) cyclicValue := by
  intro same
  have related := (ContextualCoalgebraQuotient.projection_eq_iff coalgebra (world 0) _ _).mp same
  have material := (ContextualMaterialCoalgebra.source_bisimilar_iff_reading_eq coalgebra reading
    exact_readout_square (world 0) emptyValue cyclicValue).mp related
  rw [emptyValue_readout, cyclicValue_readout] at material
  exact HSet.empty_ne_quineAtom material

end Presented

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebraControls
