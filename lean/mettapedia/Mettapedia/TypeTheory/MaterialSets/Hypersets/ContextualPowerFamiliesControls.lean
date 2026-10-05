import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualConstructiveLogic

/-!
# Infinite observed controls for contextual power families

The observed material input has a nonconstant cyclic-valued natural
section over infinitely many labelled worlds. Local power elements retain
the first label of an actual future history. These predicates have equal
empty present observations, while infinitely many of their material values
are distinct. Parallel histories have the same operational action but
different accepted future arguments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamiliesControls

open _root_.CategoryTheory
open ContextualGeneratedUniverse
open FuturePowerFamilies
open ContextualPowerFamilies
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

abbrev actualContext := context model worldCoding
abbrev domain := observedInput
abbrev powers := power domain arrowCoding

def initialPoint : actualContext.base.Elements := observedPoint model worldCoding oldRaw

def nextPoint (label : Nat) : actualContext.base.Elements :=
  ⟨next, actualContext.base.map (extension label) initialPoint.2⟩

def extensionArrow (label : Nat) : initialPoint ⟶ nextPoint label :=
  ⟨extension label, rfl⟩

def futureArgument (label : Nat) : Arguments domain.family initialPoint :=
  ⟨⟨nextPoint label, extensionArrow label⟩, positiveSection.val (nextPoint label)⟩

/-- Membership depends on the first authored history label. Later context
restriction appends history and preserves that first label. -/
def startsWith (label : Nat) : Predicate domain.family initialPoint where
  holds argument := ∃ rest, argument.1.2.val.unop.unop.val = label :: rest
  closed {first second} move available := by
    obtain ⟨rest, starts⟩ := available
    have triangle := congrArg
      (fun arrow : initialPoint ⟶ second.1.1 => arrow.val.unop.unop.val) move.1.2
    change first.1.2.val.unop.unop.val ++ move.1.1.val.unop.unop.val =
      second.1.2.val.unop.unop.val at triangle
    refine ⟨rest ++ move.1.1.val.unop.unop.val, ?_⟩
    rw [← triangle, starts]
    rfl

theorem startsWith_future_iff (label other : Nat) :
    (startsWith label).holds (futureArgument other) ↔ label = other := by
  change (∃ rest, [other] = label :: rest) ↔ label = other
  constructor
  · rintro ⟨rest, same⟩
    exact (List.cons.inj same).1.symm
  · intro same
    exact ⟨[], same ▸ rfl⟩

theorem startsWith_has_no_present_truth (label : Nat) (argument : domain.family.obj initialPoint) :
    ¬ (startsWith label).holds (current domain.family initialPoint argument) := by
  change ¬ ∃ rest, [] = label :: rest
  rintro ⟨rest, impossible⟩
  cases impossible

def materialPredicate (label : Nat) : HSet := (powers.model initialPoint).value (startsWith label)

theorem material_future_truth (label other : Nat) :
    (domain.futureCoding arrowCoding initialPoint).reading (futureArgument other) ∈ materialPredicate label ↔
      label = other :=
  (power_truth domain arrowCoding initialPoint (startsWith label) (futureArgument other)).trans
    (startsWith_future_iff label other)

/-- The carrier contains infinitely many genuinely different material
predicates even though their current observations all agree. -/
theorem materialPredicate_injective : Function.Injective materialPredicate := by
  intro first second same
  have truth : (domain.futureCoding arrowCoding initialPoint).reading (futureArgument first) ∈
      materialPredicate first := (material_future_truth first first).mpr rfl
  rw [same] at truth
  exact ((material_future_truth second first).mp truth).symm

theorem materialPredicate_member (label : Nat) :
    materialPredicate label ∈ (powers.model initialPoint).carrier :=
  (powers.model initialPoint).value_mem (startsWith label)

theorem present_part_empty (label : Nat) :
    presentPart domain arrowCoding initialPoint (startsWith label) = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value available
  obtain ⟨argument, _, present⟩ := (mem_presentPart domain arrowCoding initialPoint _ value).mp available
  exact startsWith_has_no_present_truth label argument present

theorem present_observation_not_injective :
    ¬ Function.Injective (presentPart domain arrowCoding initialPoint) := by
  intro injective
  have same := injective (a₁ := startsWith 0) (a₂ := startsWith 1)
    ((present_part_empty 0).trans (present_part_empty 1).symm)
  have material := congrArg (fun predicate => (powers.model initialPoint).value predicate) same
  exact Nat.zero_ne_one (materialPredicate_injective material)

theorem no_recovery_from_present_subset :
    ¬ ∃ recovery : HSet → HSet, ∀ predicate : powers.family.obj initialPoint,
      recovery (presentPart domain arrowCoding initialPoint predicate) =
        (powers.model initialPoint).value predicate := by
  rintro ⟨recovery, inverse⟩
  have same : materialPredicate 0 = materialPredicate 1 := by
    have first := inverse (startsWith 0)
    have second := inverse (startsWith 1)
    rw [present_part_empty] at first second
    exact first.symm.trans second
  exact Nat.zero_ne_one (materialPredicate_injective same)

/-- The source action observes endpoints and argument transport identically
along these parallel histories. The power predicates still separate them. -/
theorem parallel_action_but_different_future_truth :
    model.restrict (extension 0) oldRaw.2 = model.restrict (extension 1) oldRaw.2 ∧
      (startsWith 0).holds (futureArgument 0) ∧
      ¬ (startsWith 0).holds (futureArgument 1) :=
  ⟨parallel_actions_equal 0 1 oldRaw.2, (startsWith_future_iff 0 0).mpr rfl,
    fun holds => Nat.zero_ne_one ((startsWith_future_iff 0 1).mp holds)⟩

theorem actual_cyclic_section_varies :
    (domain.model (observedPoint model worldCoding oldRaw)).value
        (positiveSection.val (observedPoint model worldCoding oldRaw)) = ∅ ∧
    (domain.model (observedPoint model worldCoding newRaw)).value
        (positiveSection.val (observedPoint model worldCoding newRaw)) = HSet.quineAtom ∧
    (domain.model (observedPoint model worldCoding oldRaw)).value
        (positiveSection.val (observedPoint model worldCoding oldRaw)) ≠
      (domain.model (observedPoint model worldCoding newRaw)).value
        (positiveSection.val (observedPoint model worldCoding newRaw)) :=
  ⟨old_section_value, new_section_value, section_values_differ⟩

def laterTruth : ContextualSeparationCollection.StablePredicate domain where
  holds point _argument := 0 < point.1.unop.unop.length
  map {first _second} step _argument available := Nat.lt_of_lt_of_le available
    ((Nat.le_add_right first.1.unop.unop.length step.val.unop.unop.val.length).trans_eq
      step.val.unop.unop.property)

def laterTruthSection : powers.family.sections := classifierEquiv domain arrowCoding laterTruth

theorem classified_future_available (label : Nat) :
    (domain.futureCoding arrowCoding initialPoint).reading (futureArgument label) ∈
      (powers.model initialPoint).value (laterTruthSection.val initialPoint) :=
  (classifier_truth domain arrowCoding laterTruth initialPoint (futureArgument label)).mpr
    (show 0 < 1 from Nat.zero_lt_succ 0)

theorem classified_present_part_empty :
    presentPart domain arrowCoding initialPoint (laterTruthSection.val initialPoint) = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value available
  obtain ⟨argument, _, present⟩ := (mem_presentPart domain arrowCoding initialPoint _ value).mp available
  change 0 < 0 at present
  exact Nat.lt_irrefl 0 present

theorem classified_material_predicate_nonempty :
    (powers.model initialPoint).value (laterTruthSection.val initialPoint) ≠ ∅ := by
  intro empty
  have available := classified_future_available 0
  rw [empty] at available
  exact HSet.notMem_empty _ available

theorem classified_later_present_truth :
    (domain.model (nextPoint 0)).value (positiveSection.val (nextPoint 0)) ∈
      presentPart domain arrowCoding (nextPoint 0) (laterTruthSection.val (nextPoint 0)) := by
  exact (presentPart_truth domain arrowCoding (nextPoint 0)
    (laterTruthSection.val (nextPoint 0)) (positiveSection.val (nextPoint 0))).mpr
      (show 0 < 1 from Nat.zero_lt_succ 0)

/-- A genuinely natural classifier section has a growing current material
subset. Its complete future predicate was already nonempty initially. -/
theorem classified_present_values_vary :
    presentPart domain arrowCoding initialPoint (laterTruthSection.val initialPoint) ≠
      presentPart domain arrowCoding (nextPoint 0) (laterTruthSection.val (nextPoint 0)) := by
  rw [classified_present_part_empty]
  intro same
  have available := classified_later_present_truth
  rw [← same] at available
  exact HSet.notMem_empty _ available

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamiliesControls
