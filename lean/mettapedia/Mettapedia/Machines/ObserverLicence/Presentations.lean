import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Answer bags, declared orders and observer refinement

An unordered producer specifies a multiset, not a distinguished enumeration.
An ordered producer additionally specifies its enumeration. Observation is a
relation: a bag's first witness and its collapsed tuple may vary between legal
enumerations. A bag-invariant observer has the same result under either
presentation. Occurrence annotations may be included in the answer type;
forgetting them does not identify repeated occurrences in the multiset.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence

universe u v
variable {α : Type u} {β : Type v}

inductive Producer (α : Type u) where
  | bag (answers : Multiset α)
  | ordered (answers : List α)

def Producer.answers : Producer α → Multiset α
  | .bag answers => answers
  | .ordered answers => answers

def Represents : Producer α → List α → Prop
  | .bag answers, enumeration => (enumeration : Multiset α) = answers
  | .ordered answers, enumeration => enumeration = answers

def Observes (producer : Producer α) (observer : List α → β) (result : β) : Prop :=
  ∃ enumeration, Represents producer enumeration ∧ observer enumeration = result

def BagInvariant (observer : List α → β) : Prop :=
  ∀ {first second}, first.Perm second → observer first = observer second

theorem representation_exists (producer : Producer α) :
    ∃ enumeration, Represents producer enumeration := by
  cases producer with
  | bag answers => exact Quot.exists_rep answers
  | ordered answers => exact ⟨answers, rfl⟩

theorem observation_exists (producer : Producer α) (observer : List α → β) :
    ∃ result, Observes producer observer result := by
  obtain ⟨enumeration, represented⟩ := representation_exists producer
  exact ⟨observer enumeration, enumeration, represented, rfl⟩

theorem ordered_observation_iff (answers : List α) (observer : List α → β) (result : β) :
    Observes (.ordered answers) observer result ↔ observer answers = result := by
  constructor
  · rintro ⟨enumeration, rfl, observed⟩
    exact observed
  · exact fun same => ⟨answers, rfl, same⟩

theorem representation_bag (producer : Producer α) (enumeration : List α)
    (represented : Represents producer enumeration) :
    (enumeration : Multiset α) = producer.answers := by
  cases producer with
  | bag answers => exact represented
  | ordered answers => exact congrArg (fun xs : List α => (xs : Multiset α)) represented

theorem ordered_forgets (answers : List α) (observer : List α → β) (result : β)
    (observed : Observes (.ordered answers) observer result) :
    Observes (.bag (answers : Multiset α)) observer result :=
  ⟨answers, rfl, (ordered_observation_iff answers observer result).mp observed⟩

theorem invariant_refinement (answers : List α) (observer : List α → β)
    (invariant : BagInvariant observer) (result : β) :
    Observes (.ordered answers) observer result ↔
      Observes (.bag (answers : Multiset α)) observer result := by
  constructor
  · exact ordered_forgets answers observer result
  · rintro ⟨enumeration, represented, observed⟩
    have permutation : enumeration.Perm answers := Multiset.coe_eq_coe.mp represented
    exact (ordered_observation_iff answers observer result).mpr
      ((invariant permutation).symm.trans observed)

theorem invariant_observation_unique (producer : Producer α) (observer : List α → β)
    (invariant : BagInvariant observer) {first second : β}
    (one : Observes producer observer first) (two : Observes producer observer second) :
    first = second := by
  obtain ⟨left, leftRep, leftResult⟩ := one
  obtain ⟨right, rightRep, rightResult⟩ := two
  have permutation : left.Perm right := Multiset.coe_eq_coe.mp
    ((representation_bag producer left leftRep).trans
      (representation_bag producer right rightRep).symm)
  exact leftResult.symm.trans ((invariant permutation).trans rightResult)

def onBag (observer : List α → β) (invariant : BagInvariant observer) : Multiset α → β :=
  Quot.lift observer (fun _ _ permutation => invariant permutation)

theorem bag_factorization_iff (observer : List α → β) :
    (∃ factor : Multiset α → β, ∀ answers : List α, factor answers = observer answers) ↔
      BagInvariant observer := by
  constructor
  · rintro ⟨factor, computes⟩ first second permutation
    rw [← computes first, ← computes second]
    exact congrArg factor (Quot.sound permutation)
  · intro invariant
    exact ⟨onBag observer invariant, fun _ => rfl⟩

def once (answers : List α) : Option α := answers.head?
def select (number : Nat) (answers : List α) : List α := answers.take number
def collapse (answers : List α) : List α := answers
def count (answers : List α) : Nat := answers.length
def existsAnswer (answers : List α) : Bool := !answers.isEmpty

theorem ordered_once (answers : List α) (result : Option α) :
    Observes (.ordered answers) once result ↔ answers.head? = result :=
  ordered_observation_iff answers once result

theorem ordered_select (answers : List α) (number : Nat) (result : List α) :
    Observes (.ordered answers) (select number) result ↔ answers.take number = result :=
  ordered_observation_iff answers (select number) result

theorem ordered_collapse (answers result : List α) :
    Observes (.ordered answers) collapse result ↔ answers = result :=
  ordered_observation_iff answers collapse result

theorem bag_once_some (answers : Multiset α) (value : α) :
    Observes (.bag answers) once (some value) ↔ value ∈ answers := by
  constructor
  · rintro ⟨enumeration, represented, observed⟩
    have inside : value ∈ enumeration := by
      cases enumeration with
      | nil => simp [once] at observed
      | cons head rest =>
          have same : head = value := by simpa [once] using observed
          subst value
          exact List.mem_cons_self
    rw [← represented]
    exact inside
  · intro inside
    obtain ⟨rest, same⟩ := Multiset.exists_cons_of_mem inside
    obtain ⟨enumeration, represented⟩ := Quot.exists_rep rest
    change (enumeration : Multiset α) = rest at represented
    refine ⟨value :: enumeration, ?_, rfl⟩
    change value ::ₘ (enumeration : Multiset α) = answers
    rw [represented, ← same]

theorem bag_once_none (answers : Multiset α) :
    Observes (.bag answers) once none ↔ answers = 0 := by
  constructor
  · rintro ⟨enumeration, represented, observed⟩
    have empty : enumeration = [] := by
      cases enumeration with
      | nil => rfl
      | cons head rest => simp [once] at observed
    simpa [empty] using represented.symm
  · intro empty
    exact ⟨[], empty.symm, rfl⟩

theorem bag_select_iff (answers : Multiset α) (number : Nat) (selected : List α) :
    Observes (.bag answers) (select number) selected ↔
      ∃ suffix : List α, ((selected ++ suffix : List α) : Multiset α) = answers ∧
        selected.length = min number answers.card := by
  constructor
  · rintro ⟨enumeration, represented, observed⟩
    change (enumeration : Multiset α) = answers at represented
    change enumeration.take number = selected at observed
    subst selected
    refine ⟨enumeration.drop number, ?_, ?_⟩
    · simpa only [List.take_append_drop] using represented
    · have size := congrArg Multiset.card represented
      simpa only [Multiset.coe_card, List.length_take] using
        congrArg (min number) size
  · rintro ⟨suffix, represented, size⟩
    refine ⟨selected ++ suffix, represented, ?_⟩
    have total := congrArg Multiset.card represented
    simp only [Multiset.coe_card, List.length_append] at total
    change (selected ++ suffix).take number = selected
    by_cases enough : number ≤ answers.card
    · have length : selected.length = number := by omega
      rw [← length, List.take_left]
    · have empty : suffix = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [empty, List.append_nil]
      exact List.take_of_length_le (by omega)

theorem collapse_superpose (source result : List α) :
    Observes (.bag (source : Multiset α)) collapse result ↔ result.Perm source := by
  constructor
  · rintro ⟨enumeration, represented, rfl⟩
    exact Multiset.coe_eq_coe.mp represented
  · intro permutation
    exact ⟨result, Quot.sound permutation, rfl⟩

theorem superpose_collapse (answers : Multiset α) (result : List α)
    (observed : Observes (.bag answers) collapse result) :
    (result : Multiset α) = answers := by
  obtain ⟨enumeration, represented, rfl⟩ := observed
  exact represented

theorem count_invariant : BagInvariant (count : List α → Nat) :=
  fun permutation => permutation.length_eq

theorem exists_invariant : BagInvariant (existsAnswer : List α → Bool) := by
  intro first second permutation
  have sameLength := permutation.length_eq
  cases first <;> cases second <;> simp_all [existsAnswer]

theorem bag_count_iff (answers : Multiset α) (number : Nat) :
    Observes (.bag answers) count number ↔ answers.card = number := by
  constructor
  · rintro ⟨enumeration, represented, observed⟩
    rw [← represented]
    exact observed
  · intro same
    obtain ⟨enumeration, represented⟩ := representation_exists (.bag answers)
    refine ⟨enumeration, represented, ?_⟩
    change enumeration.length = number
    rw [← same, ← represented]
    rfl

theorem select_zero_invariant : BagInvariant (select 0 : List α → List α) := by
  intro first second _
  simp [select]

def Commutes (step : β → α → β) : Prop :=
  ∀ accumulator first second,
    step (step accumulator first) second = step (step accumulator second) first

theorem fold_invariant (step : β → α → β) (commutes : Commutes step) (initial : β) :
    BagInvariant (fun answers => answers.foldl step initial) := by
  let _ : RightCommutative step := ⟨commutes⟩
  intro first second permutation
  exact permutation.foldl_eq initial

namespace Controls

theorem first_is_not_bag_invariant : ¬ BagInvariant (once : List Nat → Option Nat) := by
  intro invariant
  have same := invariant (List.Perm.swap 1 2 [])
  contradiction

theorem select_is_not_bag_invariant : ¬ BagInvariant (select 2 : List Nat → List Nat) := by
  intro invariant
  have same := invariant (List.Perm.swap 1 2 [3])
  contradiction

theorem collapse_is_not_bag_invariant : ¬ BagInvariant (collapse : List Nat → List Nat) := by
  intro invariant
  have same := invariant (List.Perm.swap 1 2 [])
  contradiction

theorem an_arbitrary_fold_needs_an_order :
    ¬ BagInvariant (fun answers : List Nat => answers.foldl (fun n a => 10 * n + a) 0) := by
  intro invariant
  have same := invariant (List.Perm.swap 1 2 [])
  norm_num at same

theorem a_bag_witness_is_not_an_ordered_first :
    Observes (.bag (([1, 2] : List Nat) : Multiset Nat)) once (some 2) ∧
      ¬ Observes (.ordered [1, 2]) once (some 2) := by
  constructor
  · exact (bag_once_some _ _).mpr (by simp)
  · rw [ordered_once]
    decide

theorem multiplicity_not_just_support :
    Observes (.bag (([7, 7, 8] : List Nat) : Multiset Nat)) count 3 ∧
      ¬ Observes (.bag (([7, 8] : List Nat) : Multiset Nat)) count 3 := by
  constructor
  · exact ⟨[7, 7, 8], rfl, rfl⟩
  · intro observed
    have same := invariant_observation_unique _ count count_invariant observed
      (show Observes (.bag (([7, 8] : List Nat) : Multiset Nat)) count 2 from
        ⟨[7, 8], rfl, rfl⟩)
    contradiction

end Controls

end Mettapedia.Machines.ObserverLicence
