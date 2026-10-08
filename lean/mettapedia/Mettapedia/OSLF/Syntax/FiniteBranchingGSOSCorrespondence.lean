import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSInterpolation

/-!
# Reconstruction of finite-premise nondeterministic GSOS rules

The finite generic readout of the supplied natural law determines a bound
on target leaf occurrences. Complete generic inputs at one larger capacity
give an independently authored finite rule family. Expansion and compression
preserve every retained target name while unused positions cover the full
successor sets. These arguments establish exact denotation in both directions.

The converse in this file requires finite action carriers. Forward finite
clause instantiation permits arbitrary actions and remains separately proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.Reconstruction

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Generic Classical

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable [∀ sort, Finite (Actions sort)]

def capacity {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort) : Nat :=
  budget law guard action + 1

def bounded {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort) :=
  boundedCounts guard (capacity law guard action)

theorem capacity_pos {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort) :
    0 < capacity law guard action := Nat.succ_pos _

theorem bounded_enabled {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort) :
    enabled (bounded law guard action) = guard := by
  funext address
  cases available : guard address <;>
    simp [enabled, bounded, boundedCounts, available, capacity_pos]

theorem bounded_matches_guard {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input (pattern (bounded law guard action)) X)
    (matching : Matches (pattern (bounded law guard action)) supplied input) :
    inputGuard supplied = guard := by
  funext address
  cases available : guard address with
  | false =>
      have zero : bounded law guard action address = 0 := by
        simp [bounded, boundedCounts, available]
      have member : address ∈ (pattern (bounded law guard action)).negative :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero⟩
      simp [inputGuard, matching.2.2 address member]
  | true =>
      have positive : 0 < bounded law guard action address := by
        simpa [bounded, boundedCounts, available] using capacity_pos law guard action
      have member : input.derivatives ⟨address, ⟨0, positive⟩⟩ ∈ (supplied address.1).2 address.2 :=
        matching.2.1 ⟨address, ⟨0, positive⟩⟩
      have nonempty : (supplied address.1).2 address.2 ≠ ∅ := by
        intro empty
        rw [empty] at member
        exact Finset.notMem_empty _ member
      simp [inputGuard, nonempty]

def expanded {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    Counts (Actions := Actions) operator :=
  fun address => if guard address = true then
    budget law guard action + capacity law guard action + ((supplied address.1).2 address.2).card + 1
  else 0

theorem expanded_enabled {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    enabled (expanded law guard action supplied) = guard := by
  funext address
  cases available : guard address <;> simp [enabled, expanded, available]

theorem expanded_zero_iff {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (agrees : inputGuard supplied = guard) (address : Address (Actions := Actions) operator) :
    expanded law guard action supplied address = 0 ↔ (supplied address.1).2 address.2 = ∅ := by
  have same := congrFun agrees address
  by_cases empty : (supplied address.1).2 address.2 = ∅
  · have available : guard address = false := by simpa [inputGuard, empty] using same.symm
    simp [expanded, available, empty]
  · have available : guard address = true := by simpa [inputGuard, empty] using same.symm
    simp [expanded, available, empty]

theorem expanded_enough {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (agrees : inputGuard supplied = guard) (address : Address (Actions := Actions) operator) :
    ((supplied address.1).2 address.2).card ≤ expanded law guard action supplied address := by
  cases available : guard address with
  | true => simp [expanded, available]; omega
  | false =>
      have empty := (expanded_zero_iff law guard action supplied agrees address).mp
        (by simp [expanded, available])
      simp [expanded, available, empty]

theorem expanded_slots {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    ∃ slots : ∀ address, Fin (expanded law guard action supplied address) → Fin (bounded law guard action address),
      ∀ address, Function.Surjective (slots address) := by
  apply exists_slots
  · intro address zero
    cases available : guard address with
    | false => simp [expanded, available]
    | true =>
        have positive : 0 < bounded law guard action address := by
          simpa [bounded, boundedCounts, available] using capacity_pos law guard action
        omega
  · intro address
    cases available : guard address <;> simp [expanded, bounded, boundedCounts, available]
    omega

theorem firing_assignment {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) {X : S.Families}
    (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input (pattern counts) X) (matching : Matches (pattern counts) supplied input) :
    input.assignment = assignment counts (fun position => (supplied position).1)
      (fun address slot => input.derivatives ⟨address, slot⟩) := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro value
  cases base
  cases value with
  | original position => exact matching.1 position
  | derivative occurrence => rfl

/-- Every reconstructed clause remains sound when its positive successors
occupy only part of a larger independently supplied successor set. -/
theorem sound {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (guard : Guard (Actions := Actions) operator) (action : Actions sort)
    (target : S.Term (Family (bounded law guard action)) sort)
    (member : target ∈ readout law (bounded law guard action) action)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input (pattern (bounded law guard action)) X)
    (matching : Matches (pattern (bounded law guard action)) supplied input) :
    S.rename input.assignment target ∈ law.app X PUnit.unit sort ⟨operator, supplied⟩ action := by
  have agrees := bounded_matches_guard law guard action supplied input matching
  obtain ⟨slots, surjective⟩ := expanded_slots law guard action supplied
  have image := readout_slotAssignment law (expanded law guard action supplied) (bounded law guard action)
    action slots surjective
  have memberImage : target ∈ Mettapedia.CategoryTheory.FinitePowerset.map
      (S.rename (slotAssignment _ _ slots)) (readout law (expanded law guard action supplied) action) := by
    rw [image]
    exact member
  obtain ⟨earlier, earlierMember, same⟩ :=
    (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mp memberImage
  have leafBound : leafCount earlier ≤ budget law guard action := by
    simpa only [expanded_enabled] using leafCount_le_budget law _ action earlier earlierMember
  let reading := fun address slot => input.derivatives ⟨address, slots address slot⟩
  have readingMember : ∀ address slot, reading address slot ∈ (supplied address.1).2 address.2 :=
    fun address slot => matching.2.1 ⟨address, slots address slot⟩
  have zero : ∀ address, expanded law guard action supplied address = 0 →
      (supplied address.1).2 address.2 = ∅ :=
    fun address => (expanded_zero_iff law guard action supplied agrees address).mp
  have room : ∀ address, (usedSlots earlier address).card + ((supplied address.1).2 address.2).card ≤
      expanded law guard action supplied address := by
    intro address
    have bound := (usedSlots_card_le earlier address).trans leafBound
    cases available : guard address with
    | true => simp [expanded, available]; omega
    | false =>
        have countZero : expanded law guard action supplied address = 0 := by simp [expanded, available]
        have usedZero : (usedSlots earlier address).card = 0 := by
          have bound := usedSlots_card_le_count earlier address
          omega
        simp [expanded, available, usedZero, zero address countZero]
  obtain ⟨values, covers, retained⟩ :=
    interpolate_successors _ earlier supplied reading readingMember zero room
  have complete := readout_assignment law (expanded law guard action supplied) action supplied values covers
  have finalMember : S.rename (assignment _ (fun position => (supplied position).1) values) earlier ∈
      law.app X PUnit.unit sort ⟨operator, supplied⟩ action := by
    rw [← complete]
    exact (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mpr ⟨earlier, earlierMember, rfl⟩
  have retainedTree := rename_assignment_eq earlier (fun position => (supplied position).1)
    values reading retained
  have composed : S.rename (assignment _ (fun position => (supplied position).1) reading) earlier =
      S.rename input.assignment (S.rename (slotAssignment _ _ slots) earlier) := by
    rw [firing_assignment _ supplied input matching]
    exact (rename_slots _ _ slots (fun position => (supplied position).1)
      (fun address slot => input.derivatives ⟨address, slot⟩) earlier).symm
  rw [retainedTree, composed, same] at finalMember
  exact finalMember

/-- Every actual law target has a finite reconstructed firing. Complete
input behavior is first expanded; bounded names then retain the full target. -/
theorem complete {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (action : Actions sort) {X : S.Families}
    (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (target : S.Term X sort)
    (member : target ∈ law.app X PUnit.unit sort ⟨operator, supplied⟩ action) :
    ∃ body : S.Term (Family (bounded law (inputGuard supplied) action)) sort,
      body ∈ readout law (bounded law (inputGuard supplied) action) action ∧
      ∃ input : Input (pattern (bounded law (inputGuard supplied) action)) X,
        Matches (pattern (bounded law (inputGuard supplied) action)) supplied input ∧
          S.rename input.assignment body = target := by
  let guard := inputGuard supplied
  obtain ⟨reading, covers⟩ := exists_successors (expanded law guard action supplied) supplied
    (expanded_zero_iff law guard action supplied rfl) (expanded_enough law guard action supplied rfl)
  have completeReadout := readout_assignment law (expanded law guard action supplied) action supplied reading covers
  have memberImage : target ∈ Mettapedia.CategoryTheory.FinitePowerset.map
      (S.rename (assignment _ (fun position => (supplied position).1) reading))
      (readout law (expanded law guard action supplied) action) := by
    rw [completeReadout]
    exact member
  obtain ⟨earlier, earlierMember, same⟩ :=
    (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mp memberImage
  have leafBound : leafCount earlier ≤ budget law guard action := by
    simpa only [expanded_enabled] using leafCount_le_budget law _ action earlier earlierMember
  have readingMember : ∀ address slot, reading address slot ∈ (supplied address.1).2 address.2 := by
    intro address slot
    rw [← covers address]
    exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩
  have zero : ∀ address, bounded law guard action address = 0 ↔ expanded law guard action supplied address = 0 := by
    intro address
    cases available : guard address <;>
      simp [bounded, boundedCounts, expanded, available, capacity]
  have names : ∀ address, (usedSlots earlier address).card ≤ bounded law guard action address := by
    intro address
    have bound := (usedSlots_card_le earlier address).trans leafBound
    cases available : guard address with
    | true => simp [bounded, boundedCounts, available, capacity]; omega
    | false =>
        have countZero : expanded law guard action supplied address = 0 := by simp [expanded, available]
        have bound := usedSlots_card_le_count earlier address
        simpa only [bounded, boundedCounts, available, Bool.false_eq_true, if_false] using
          (countZero ▸ bound)
  have room : ∀ address, (usedSlots earlier address).card + bounded law guard action address ≤
      expanded law guard action supplied address := by
    intro address
    have bound := (usedSlots_card_le earlier address).trans leafBound
    cases available : guard address with
    | true => simp [bounded, boundedCounts, expanded, available]; omega
    | false =>
        have countZero : expanded law guard action supplied address = 0 := by simp [expanded, available]
        have bound := usedSlots_card_le_count earlier address
        have usedZero : (usedSlots earlier address).card = 0 := by omega
        simp [bounded, boundedCounts, expanded, available, usedZero]
  obtain ⟨slots, values, surjective, valuesMember, retained⟩ :=
    factor_successors _ (bounded law guard action) earlier supplied reading readingMember zero names room
  let body := S.rename (slotAssignment _ _ slots) earlier
  have bodyMember : body ∈ readout law (bounded law guard action) action := by
    rw [← readout_slotAssignment law _ _ action slots surjective]
    exact (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mpr ⟨earlier, earlierMember, rfl⟩
  let input : Input (pattern (bounded law guard action)) X :=
    ⟨fun position => (supplied position).1, fun occurrence => values occurrence.1 occurrence.2⟩
  have matching : Matches (pattern (bounded law guard action)) supplied input := by
    refine ⟨fun _ => rfl, fun occurrence => valuesMember occurrence.1 occurrence.2, ?_⟩
    intro address held
    have boundedZero := (Finset.mem_filter.mp held).2
    exact (expanded_zero_iff law guard action supplied rfl address).mp ((zero address).mp boundedZero)
  refine ⟨body, bodyMember, input, matching, ?_⟩
  have composed : S.rename input.assignment body =
      S.rename (assignment _ (fun position => (supplied position).1)
        (fun address slot => values address (slots address slot))) earlier := by
    rw [firing_assignment _ supplied input matching]
    exact rename_slots _ _ slots (fun position => (supplied position).1) values earlier
  rw [composed, rename_assignment_eq earlier (fun position => (supplied position).1)
    (fun address slot => values address (slots address slot)) reading retained]
  exact same

/-- A finite family of actual syntax clauses reconstructed independently
at every complete finite availability pattern. -/
def fromLaw (law : Law S Actions) : Presentation S Actions :=
  fun _sort operator action => Finset.univ.biUnion (fun guard : Guard (Actions := Actions) operator =>
    (readout law (bounded law guard action) action).image (fun target =>
      (⟨pattern (bounded law guard action), target⟩ : Rule operator)))

/-- Exact whole-target denotation follows from support-preserving expansion
and compression, without a supplied reconstruction or soundness field. -/
theorem fromLaw_denotes (law : Law S Actions) : Presentation.Denotes (fromLaw law) law := by
  intro X sort operator supplied action target
  constructor
  · intro member
    obtain ⟨body, bodyMember, input, matching, same⟩ := complete law action supplied target member
    exact ⟨⟨pattern (bounded law (inputGuard supplied) action), body⟩,
      Finset.mem_biUnion.mpr ⟨inputGuard supplied, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨body, bodyMember, rfl⟩⟩, input, matching, same⟩
  · rintro ⟨rule, member, input, matching, same⟩
    obtain ⟨guard, _, member⟩ := Finset.mem_biUnion.mp member
    obtain ⟨body, bodyMember, identified⟩ := Finset.mem_image.mp member
    subst rule
    rw [← same]
    exact sound law guard action body bodyMember supplied input matching

theorem law_roundtrip (law : Law S Actions) : Presentation.toLaw (fromLaw law) = law :=
  (Presentation.law_unique (fromLaw law) law (fromLaw_denotes law)).symm

end Mettapedia.OSLF.FiniteBranching.Premises.Reconstruction
