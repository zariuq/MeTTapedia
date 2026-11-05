import Mettapedia.Algebra.Collections.Unification
import Mettapedia.Algebra.Collections.FlatElementEncoding

/-!
# Symbolic unifier families for two flat bags with independent rests

Partial occurrence matchings determine element equations. The existing total
first-order solver either rejects those equations or produces their element
MGU. Each retained family assigns the two independent rest slots the opposite
unmatched bag plus one common bag parameter. Rest slots and that parameter
are typed separately from element variables; repeated element variables are
preserved. This is not arbitrary nested associative-commutative unification.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FlatBagUnifiers

open FlatElementEncoding (Element apply)
open Unification (matchings flat_bag_unify_iff)

inductive RestSlot where
  | left
  | right
  deriving DecidableEq, Repr

@[ext] structure Answer (A X : Type*) where
  elements : X → Element A X
  rest : RestSlot → Multiset (Element A X)

@[ext] structure Family (A X : Type*) where
  elements : X → Element A X
  base : RestSlot → Multiset (Element A X)

variable {A X : Type*}

def instantiate (family : Family A X) (remainder : X → Element A X)
    (common : Multiset (Element A X)) : Answer A X where
  elements name := apply remainder (family.elements name)
  rest slot := (family.base slot).map (apply remainder) + common

def genericAnswer (family : Family A X) : Answer A X := ⟨family.elements, family.base⟩

def Instance (family : Family A X) (answer : Answer A X) : Prop :=
  ∃ remainder common, answer = instantiate family remainder common

def MoreGeneral (general specific : Family A X) : Prop := Instance general (genericAnswer specific)

theorem instantiate_id (family : Family A X) : instantiate family Sum.inr 0 = genericAnswer family := by
  apply Answer.ext
  · funext name
    simp [instantiate, genericAnswer]
  · funext slot
    simp [instantiate, genericAnswer]

theorem generic_instance (family : Family A X) : Instance family (genericAnswer family) :=
  ⟨Sum.inr, 0, (instantiate_id family).symm⟩

theorem instance_factor {general specific : Family A X} {answer : Answer A X}
    (covers : MoreGeneral general specific) (instanceOf : Instance specific answer) : Instance general answer := by
  obtain ⟨first, commonFirst, represented⟩ := covers
  obtain ⟨second, commonSecond, rfl⟩ := instanceOf
  have elements := congrArg Answer.elements represented
  have rests := congrArg Answer.rest represented
  refine ⟨fun name => apply second (first name), commonFirst.map (apply second) + commonSecond, ?_⟩
  apply Answer.ext
  · funext name
    change apply second (specific.elements name) = apply (fun name => apply second (first name)) (general.elements name)
    have same := congrFun elements name
    change specific.elements name = apply first (general.elements name) at same
    rw [same, FlatElementEncoding.apply_comp]
  · funext slot
    have same := congrFun rests slot
    change specific.base slot = (general.base slot).map (apply first) + commonFirst at same
    simp only [instantiate, same, Multiset.map_add, Multiset.map_map, add_assoc]
    congr 1
    apply Multiset.map_congr rfl
    intro element _
    exact (FlatElementEncoding.apply_comp second first element).symm

theorem MoreGeneral.refl (family : Family A X) : MoreGeneral family family := generic_instance family

theorem MoreGeneral.trans {first second third : Family A X}
    (earlier : MoreGeneral first second) (later : MoreGeneral second third) : MoreGeneral first third :=
  instance_factor earlier later

theorem moreGeneral_iff_instances_subset (general specific : Family A X) :
    MoreGeneral general specific ↔ ∀ answer, Instance specific answer → Instance general answer :=
  ⟨fun covers _ instanceOf => instance_factor covers instanceOf,
    fun included => included (genericAnswer specific) (generic_instance specific)⟩

def Solves (left right : List (Element A X)) (answer : Answer A X) : Prop :=
  (left.map (apply answer.elements) : Multiset (Element A X)) + answer.rest .left =
    (right.map (apply answer.elements) : Multiset (Element A X)) + answer.rest .right

abbrev Matching (A X : Type*) :=
  List (Element A X × Element A X) × List (Element A X) × List (Element A X)

def fromMatching (matching : Matching A X) (general : X → Element A X) : Family A X where
  elements := general
  base
    | .left => (matching.2.2.map (apply general) : Multiset (Element A X))
    | .right => (matching.2.1.map (apply general) : Multiset (Element A X))

variable [DecidableEq A] [DecidableEq X]

def candidate (matching : Matching A X) : Option (Family A X) :=
  (FlatElementEncoding.solve matching.1).map (fromMatching matching)

/-- Finite occurrence search with an actual total element solver. No
semantic solution predicate is used to choose or validate a family. -/
def families (left right : List (Element A X)) : List (Family A X) :=
  (matchings left right).filterMap candidate

theorem fromMatching_sound (left right : List (Element A X)) (matching : Matching A X)
    (member : matching ∈ matchings left right) (general : X → Element A X)
    (accepted : FlatElementEncoding.solve matching.1 = some general)
    (answer : Answer A X) (instanceOf : Instance (fromMatching matching general) answer) : Solves left right answer := by
  obtain ⟨remainder, common, rfl⟩ := instanceOf
  have paired := FlatElementEncoding.solve_sound matching.1 general accepted
  have composite : (fun element => apply remainder (apply general element)) =
      apply (fun name => apply remainder (general name)) :=
    funext fun element => (FlatElementEncoding.apply_comp remainder general element).symm
  apply (flat_bag_unify_iff (apply (fun name => apply remainder (general name))) left right _ _).mpr
  refine ⟨matching, member, ?_, common, ?_, ?_⟩
  · intro pair present
    rw [FlatElementEncoding.apply_comp, FlatElementEncoding.apply_comp, paired pair present]
  · simp only [instantiate, fromMatching, Multiset.map_coe, List.map_map, Function.comp_def, composite]
  · simp only [instantiate, fromMatching, Multiset.map_coe, List.map_map, Function.comp_def, composite]

theorem sound (left right : List (Element A X)) (family : Family A X)
    (member : family ∈ families left right) (answer : Answer A X) (instanceOf : Instance family answer) :
    Solves left right answer := by
  obtain ⟨matching, selected, produced⟩ := List.mem_filterMap.mp member
  unfold candidate at produced
  obtain ⟨general, accepted, rfl⟩ := Option.map_eq_some_iff.mp produced
  exact fromMatching_sound left right matching selected general accepted answer instanceOf

/-- Every symbolic solution, including repeated element-variable captures,
factors through a family returned by the actual finite search. -/
theorem complete (left right : List (Element A X)) (answer : Answer A X) (solved : Solves left right answer) :
    ∃ family ∈ families left right, Instance family answer := by
  obtain ⟨matching, member, paired, common, leftRest, rightRest⟩ :=
    (flat_bag_unify_iff (apply answer.elements) left right (answer.rest .left) (answer.rest .right)).mp solved
  obtain ⟨general, accepted⟩ := FlatElementEncoding.solve_complete matching.1 answer.elements paired
  obtain ⟨remainder, factors⟩ := FlatElementEncoding.solve_mgu matching.1 general accepted answer.elements paired
  have element_factor (element : Element A X) :
      apply answer.elements element = apply remainder (apply general element) := by
    cases element with
    | inl => rfl
    | inr name => exact factors name
  refine ⟨fromMatching matching general, List.mem_filterMap.mpr ⟨matching, member, ?_⟩,
    remainder, common, ?_⟩
  · simp only [candidate, accepted, Option.map_some]
  · apply Answer.ext
    · funext name
      exact factors name
    · funext slot
      cases slot with
      | left =>
          rw [leftRest]
          simp only [instantiate, fromMatching, Multiset.map_coe, List.map_map, Function.comp_def, ← element_factor]
      | right =>
          rw [rightRest]
          simp only [instantiate, fromMatching, Multiset.map_coe, List.map_map, Function.comp_def, ← element_factor]

theorem solves_iff (left right : List (Element A X)) (answer : Answer A X) :
    Solves left right answer ↔ ∃ family ∈ families left right, Instance family answer :=
  ⟨complete left right answer, fun ⟨family, member, instanceOf⟩ => sound left right family member answer instanceOf⟩

theorem finite_families (left right : List (Element A X)) :
    {family | family ∈ families left right}.Finite := (families left right).finite_toSet

theorem generated_family_solves (left right : List (Element A X)) (family : Family A X)
    (member : family ∈ families left right) : Solves left right (genericAnswer family) :=
  sound left right family member (genericAnswer family) (generic_instance family)

namespace Controls

def repeatedLeft : List (Element Nat (Fin 1)) := [.inr 0, .inr 0]
def equalRight : List (Element Nat (Fin 1)) := [.inl 1, .inl 1]
def conflicting : Matching Nat (Fin 1) := ([(.inr 0, .inl 1), (.inr 0, .inl 2)], [], [])
def consistent : Matching Nat (Fin 1) := ([(.inr 0, .inl 1), (.inr 0, .inl 1)], [], [])

theorem repeated_variable_conflict_is_discarded : candidate conflicting = none := by
  have rejected : FlatElementEncoding.solve conflicting.1 = none := by
    apply (FlatElementEncoding.solve_none_iff _).mpr
    rintro ⟨assignment, solved⟩
    have first := solved (.inr 0, .inl 1) (by simp [conflicting])
    have second := solved (.inr 0, .inl 2) (by simp [conflicting])
    have impossible : (Sum.inl 1 : Element Nat (Fin 1)) = .inl 2 := first.symm.trans second
    exact (by decide : (Sum.inl 1 : Element Nat (Fin 1)) ≠ .inl 2) impossible
  simp only [candidate, rejected, Option.map_none]

theorem repeated_equal_capture_is_retained :
    ∃ family, candidate consistent = some family ∧ family ∈ families repeatedLeft equalRight := by
  let assignment : Fin 1 → Element Nat (Fin 1) := fun _ => .inl 1
  have solved : FlatElementEncoding.Solves consistent.1 assignment := by
    intro pair member
    simp only [consistent, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  obtain ⟨general, accepted⟩ := FlatElementEncoding.solve_complete consistent.1 assignment solved
  have produced : candidate consistent = some (fromMatching consistent general) := by
    simp only [candidate, accepted, Option.map_some]
  exact ⟨_, produced, List.mem_filterMap.mpr ⟨consistent,
    by simp [consistent, repeatedLeft, equalRight, matchings, List.finRange_succ], produced⟩⟩

def compensated : Answer Nat (Fin 1) := {
  elements := Sum.inr
  rest
    | .left => {.inl 2}
    | .right => {.inl 1} }

/-- Independent rests can compensate different constants. Rejecting their
paired branch does not make the whole open-rest equation inconsistent. -/
theorem different_constants_still_have_a_family :
    ∃ family ∈ families [.inl 1] [.inl 2], Instance family compensated := by
  apply complete
  change ({Sum.inl 1} : Multiset (Element Nat (Fin 1))) + {.inl 2} = {.inl 2} + {.inl 1}
  exact add_comm _ _

omit [DecidableEq A] [DecidableEq X] in
/-- Identifying the two input rests adds a real constraint. The independent
rest family cannot silently be reused as an aliased-rest solution. -/
theorem shared_rest_cannot_compensate_distinct_constants (left right : A) (different : left ≠ right)
    (answer : Answer A X) (sameRest : answer.rest .left = answer.rest .right) :
    ¬ Solves [.inl left] [.inl right] answer := by
  intro solved
  change ({Sum.inl left} : Multiset (Element A X)) + answer.rest .left = {.inl right} + answer.rest .right at solved
  rw [sameRest] at solved
  exact different (Sum.inl.inj (Multiset.singleton_inj.mp (add_right_cancel solved)))

end Controls

#print axioms sound
#print axioms complete
#print axioms solves_iff
#print axioms instance_factor
#print axioms Controls.shared_rest_cannot_compensate_distinct_constants

end Mettapedia.Algebra.Collections.FlatBagUnifiers
