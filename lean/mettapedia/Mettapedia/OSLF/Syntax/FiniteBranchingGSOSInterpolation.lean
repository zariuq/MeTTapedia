import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSGenericInputs

/-!
# Complete successor interpolation for finite GSOS readouts

Surjective slot maps transport complete generic behavior through the actual
natural law. Additional unused slots can cover an independently supplied
successor set while agreeing on every name read by the target. Conversely,
a bounded name carrier can retain those names and still receive a surjective
slot map. Complete target equality is obtained from finite tree support.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.Generic

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Classical

universe u v

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable [∀ sort, Finite (Actions sort)]

theorem image_values {D : Type v} [Fintype D] {V : Type u} (values : Finset V)
    (reading : D → {value // value ∈ values}) (surjective : Function.Surjective reading) :
    Finset.univ.image (fun position => (reading position).val) = values := by
  apply Finset.ext
  intro value
  rw [Finset.mem_image]
  constructor
  · rintro ⟨position, _, rfl⟩
    exact (reading position).property
  · intro member
    obtain ⟨position, same⟩ := surjective ⟨value, member⟩
    exact ⟨position, Finset.mem_univ _, congrArg Subtype.val same⟩

def slotAssignment {sort : S.Srt} {operator : S.Operator sort}
    (counts next : Counts (Actions := Actions) operator)
    (slots : ∀ address, Fin (counts address) → Fin (next address)) : Family counts ⟶ Family next :=
  assignment counts (fun position => .original position)
    (fun address slot => Variable.derivative (pattern := pattern next) ⟨address, slots address slot⟩)

theorem assignment_comp_slots {sort : S.Srt} {operator : S.Operator sort}
    (counts next : Counts (Actions := Actions) operator)
    (slots : ∀ address, Fin (counts address) → Fin (next address))
    {X : S.Families} (originals : S.Arguments X operator)
    (reading : ∀ address, Fin (next address) → X PUnit.unit (S.argument operator address.1)) :
    slotAssignment counts next slots ≫ assignment next originals reading =
      assignment counts originals (fun address slot => reading address (slots address slot)) := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro value
  cases base
  cases value <;> rfl

theorem rename_slots {sort : S.Srt} {operator : S.Operator sort}
    (counts next : Counts (Actions := Actions) operator)
    (slots : ∀ address, Fin (counts address) → Fin (next address))
    {X : S.Families} (originals : S.Arguments X operator)
    (reading : ∀ address, Fin (next address) → X PUnit.unit (S.argument operator address.1))
    (term : S.Term (Family counts) sort) :
    S.rename (assignment next originals reading) (S.rename (slotAssignment counts next slots) term) =
      S.rename (assignment counts originals (fun address slot => reading address (slots address slot))) term := by
  have composed := IndexedPolynomial.Free.map_comp S.polynomial
    (fun base index => slotAssignment counts next slots base index)
    (fun base index => assignment next originals reading base index) term
  change _ = S.rename (slotAssignment counts next slots ≫ assignment next originals reading) term at composed
  rw [assignment_comp_slots] at composed
  exact composed

theorem slotAssignment_arguments {sort : S.Srt} {operator : S.Operator sort}
    (counts next : Counts (Actions := Actions) operator)
    (slots : ∀ address, Fin (counts address) → Fin (next address))
    (surjective : ∀ address, Function.Surjective (slots address)) :
    mapArguments (slotAssignment counts next slots) (arguments counts) = arguments next := by
  unfold slotAssignment
  refine assigned_arguments counts (arguments next)
    (fun address slot => Variable.derivative (pattern := pattern next) ⟨address, slots address slot⟩) ?_
  intro address
  dsimp only [arguments]
  apply Finset.ext
  intro value
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨slot, rfl⟩
    exact ⟨slots address slot, rfl⟩
  · rintro ⟨slot, rfl⟩
    obtain ⟨earlier, rfl⟩ := surjective address slot
    exact ⟨earlier, rfl⟩

theorem readout_slotAssignment {sort : S.Srt} {operator : S.Operator sort}
    (law : Law S Actions) (counts next : Counts (Actions := Actions) operator) (action : Actions sort)
    (slots : ∀ address, Fin (counts address) → Fin (next address))
    (surjective : ∀ address, Function.Surjective (slots address)) :
    Mettapedia.CategoryTheory.FinitePowerset.map (S.rename (slotAssignment counts next slots))
      (readout law counts action) = readout law next action := by
  have natural := congrArg (fun mapping => mapping PUnit.unit sort ⟨operator, arguments counts⟩ action)
    (law.naturality (slotAssignment counts next slots))
  change law.app _ PUnit.unit sort ⟨operator,
      mapArguments (slotAssignment counts next slots) (arguments counts)⟩ action = _ at natural
  rw [slotAssignment_arguments counts next slots surjective] at natural
  exact natural.symm

omit [∀ sort, Finite (Actions sort)] in
theorem exists_slots {sort : S.Srt} {operator : S.Operator sort}
    (counts next : Counts (Actions := Actions) operator)
    (zero : ∀ address, next address = 0 → counts address = 0)
    (enough : ∀ address, next address ≤ counts address) :
    ∃ slots : ∀ address, Fin (counts address) → Fin (next address),
      ∀ address, Function.Surjective (slots address) := by
  have each : ∀ address, ∃ slots : Fin (counts address) → Fin (next address), Function.Surjective slots := by
    intro address
    by_cases positive : 0 < next address
    · refine ⟨fun slot => ⟨slot.val % next address, Nat.mod_lt _ positive⟩, ?_⟩
      intro target
      refine ⟨⟨target.val, Nat.lt_of_lt_of_le target.isLt (enough address)⟩, ?_⟩
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt
    · have nextZero : next address = 0 := by omega
      have sourceZero := zero address nextZero
      refine ⟨fun slot => (False.elim (by have impossible := slot.isLt; omega)), ?_⟩
      intro slot
      exact (False.elim (by have impossible := slot.isLt; omega))
  exact ⟨fun address => (each address).choose, fun address => (each address).choose_spec⟩

omit [∀ sort, Finite (Actions sort)] in
/-- Enumerate every supplied successor without equating independent occurrences. -/
theorem exists_successors {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) {X : S.Families}
    (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (zero : ∀ address, counts address = 0 ↔ (supplied address.1).2 address.2 = ∅)
    (enough : ∀ address, ((supplied address.1).2 address.2).card ≤ counts address) :
    ∃ values : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1),
      ∀ address, Finset.univ.image (values address) = (supplied address.1).2 address.2 := by
  have each : ∀ address, ∃ values : Fin (counts address) → X PUnit.unit (S.argument operator address.1),
      Finset.univ.image values = (supplied address.1).2 address.2 := by
    intro address
    by_cases empty : (supplied address.1).2 address.2 = ∅
    · have sourceZero := (zero address).mpr empty
      refine ⟨fun slot => (False.elim (by have impossible := slot.isLt; omega)), ?_⟩
      rw [empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro value held
      obtain ⟨slot, _, _⟩ := Finset.mem_image.mp held
      have impossible := slot.isLt
      omega
    · let targets := (supplied address.1).2 address.2
      obtain ⟨seed, seedMember⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      let _ : Nonempty {value // value ∈ targets} := ⟨⟨seed, seedMember⟩⟩
      obtain ⟨values, surjective, _⟩ :=
        Mettapedia.CategoryTheory.FiniteSupportInterpolation.surjective_extension
          (∅ : Finset (Fin (counts address))) (fun _ => (⟨seed, seedMember⟩ : {value // value ∈ targets}))
          (by simpa only [Finset.card_empty, zero_add, Fintype.card_coe, Fintype.card_fin]
            using enough address)
      exact ⟨fun slot => (values slot).val, image_values targets values surjective⟩
  exact ⟨fun address => (each address).choose, fun address => (each address).choose_spec⟩

/-- Complete coverage may be altered away from the exact target support. -/
theorem interpolate_successors {sort : S.Srt} {operator : S.Operator sort}
    (counts : Counts (Actions := Actions) operator) (term : S.Term (Family counts) sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (reading : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1))
    (member : ∀ address slot, reading address slot ∈ (supplied address.1).2 address.2)
    (zero : ∀ address, counts address = 0 → (supplied address.1).2 address.2 = ∅)
    (room : ∀ address, (usedSlots term address).card + ((supplied address.1).2 address.2).card ≤ counts address) :
    ∃ result : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1),
      (∀ address, Finset.univ.image (result address) = (supplied address.1).2 address.2) ∧
        ∀ address slot, slot ∈ usedSlots term address → result address slot = reading address slot := by
  have each : ∀ address, ∃ result : Fin (counts address) → X PUnit.unit (S.argument operator address.1),
      Finset.univ.image result = (supplied address.1).2 address.2 ∧
        ∀ slot ∈ usedSlots term address, result slot = reading address slot := by
    intro address
    by_cases positive : 0 < counts address
    · let values := (supplied address.1).2 address.2
      let _ : Nonempty {value // value ∈ values} :=
        ⟨⟨reading address ⟨0, positive⟩, member address ⟨0, positive⟩⟩⟩
      obtain ⟨result, surjective, agrees⟩ :=
        Mettapedia.CategoryTheory.FiniteSupportInterpolation.surjective_extension
          (usedSlots term address) (fun slot => (⟨reading address slot, member address slot⟩ :
            {value // value ∈ values}))
          (by simpa only [Fintype.card_coe, Fintype.card_fin] using room address)
      exact ⟨fun slot => (result slot).val, image_values values result surjective,
        fun slot held => congrArg Subtype.val (agrees slot held)⟩
    · have sourceZero : counts address = 0 := by omega
      let result : Fin (counts address) → X PUnit.unit (S.argument operator address.1) :=
        fun slot => (False.elim (by have impossible := slot.isLt; omega))
      refine ⟨result, ?_, ?_⟩
      · rw [zero address sourceZero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro value held
        obtain ⟨slot, _, _⟩ := Finset.mem_image.mp held
        have impossible := slot.isLt
        omega
      · intro slot _
        exact (False.elim (by have impossible := slot.isLt; omega))
  exact ⟨fun address => (each address).choose, fun address => (each address).choose_spec.1,
    fun address slot held => (each address).choose_spec.2 slot held⟩

/-- Compress the retained target names into a bounded intermediary while
preserving complete surjectivity and the independently supplied values. -/
theorem factor_successors {sort : S.Srt} {operator : S.Operator sort}
    (counts next : Counts (Actions := Actions) operator) (term : S.Term (Family counts) sort)
    {X : S.Families} (supplied : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (reading : ∀ address, Fin (counts address) → X PUnit.unit (S.argument operator address.1))
    (member : ∀ address slot, reading address slot ∈ (supplied address.1).2 address.2)
    (zero : ∀ address, next address = 0 ↔ counts address = 0)
    (names : ∀ address, (usedSlots term address).card ≤ next address)
    (room : ∀ address, (usedSlots term address).card + next address ≤ counts address) :
    ∃ slots : ∀ address, Fin (counts address) → Fin (next address),
      ∃ values : ∀ address, Fin (next address) → X PUnit.unit (S.argument operator address.1),
        (∀ address, Function.Surjective (slots address)) ∧
        (∀ address slot, values address slot ∈ (supplied address.1).2 address.2) ∧
        ∀ address slot, slot ∈ usedSlots term address →
          values address (slots address slot) = reading address slot := by
  have each : ∀ address,
      ∃ slots : Fin (counts address) → Fin (next address),
        ∃ values : Fin (next address) → X PUnit.unit (S.argument operator address.1),
          Function.Surjective slots ∧
          (∀ slot, values slot ∈ (supplied address.1).2 address.2) ∧
          ∀ slot ∈ usedSlots term address, values (slots slot) = reading address slot := by
    intro address
    by_cases positive : 0 < next address
    · have sourcePositive : 0 < counts address := by
        have possible := zero address
        omega
      let targets := (supplied address.1).2 address.2
      let _ : Nonempty {value // value ∈ targets} :=
        ⟨⟨reading address ⟨0, sourcePositive⟩, member address ⟨0, sourcePositive⟩⟩⟩
      obtain ⟨slots, values, surjective, agrees⟩ :=
        Mettapedia.CategoryTheory.FiniteSupportInterpolation.factor_through
          (usedSlots term address)
          (fun slot => (⟨reading address slot, member address slot⟩ : {value // value ∈ targets}))
          (next address) positive (names address)
          (by simpa only [Fintype.card_fin] using room address)
      exact ⟨slots, fun slot => (values slot).val, surjective,
        fun slot => (values slot).property,
        fun slot held => congrArg Subtype.val (agrees slot held)⟩
    · have targetZero : next address = 0 := by omega
      have sourceZero := (zero address).mp targetZero
      refine ⟨fun slot => (False.elim (by have impossible := slot.isLt; omega)),
        fun slot => (False.elim (by have impossible := slot.isLt; omega)), ?_, ?_, ?_⟩
      · intro slot
        exact (False.elim (by have impossible := slot.isLt; omega))
      · intro slot
        exact (False.elim (by have impossible := slot.isLt; omega))
      · intro slot _
        exact (False.elim (by have impossible := slot.isLt; omega))
  refine ⟨fun address => (each address).choose,
    fun address => (each address).choose_spec.choose, ?_, ?_, ?_⟩
  · intro address
    exact (each address).choose_spec.choose_spec.1
  · intro address slot
    exact (each address).choose_spec.choose_spec.2.1 slot
  · intro address slot held
    exact (each address).choose_spec.choose_spec.2.2 slot held

end Mettapedia.OSLF.FiniteBranching.Premises.Generic
