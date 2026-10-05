import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Finite interval classes with explicit universes

The implementations below construct interval lists. Membership specifications
are independent predicates, not definitions of the operations under test.
Code-point and scalar universes are distinct; complements are relative to the
chosen universe. These are algorithm laws, not a C memory-safety refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.IntervalClasses

structure Interval where
  low : Nat
  high : Nat
  deriving DecidableEq, Repr

def Interval.Valid (r : Interval) : Prop := r.low ≤ r.high

def Interval.Contains (r : Interval) (x : Nat) : Prop := r.low ≤ x ∧ x ≤ r.high

def Contains (ranges : List Interval) (x : Nat) : Prop :=
  ∃ r ∈ ranges, r.Contains x

def Valid (ranges : List Interval) : Prop := ∀ r ∈ ranges, r.Valid

@[simp] theorem contains_nil (x : Nat) : ¬ Contains [] x := by simp [Contains]

@[simp] theorem contains_cons (r : Interval) (rs : List Interval) (x : Nat) :
    Contains (r :: rs) x ↔ r.Contains x ∨ Contains rs x := by
  simp [Contains]

@[simp] theorem contains_append (a b : List Interval) (x : Nat) :
    Contains (a ++ b) x ↔ Contains a x ∨ Contains b x := by
  simp only [Contains, List.mem_append]
  aesop

theorem contains_flatMap (rs : List Interval) (f : Interval → List Interval) (x : Nat) :
    Contains (rs.flatMap f) x ↔ ∃ r ∈ rs, Contains (f r) x := by
  simp only [Contains, List.mem_flatMap]
  aesop

def intersectInterval (a b : Interval) : List Interval :=
  let low := max a.low b.low
  let high := min a.high b.high
  if low ≤ high then [⟨low, high⟩] else []

theorem intersectInterval_contains (a b : Interval) (x : Nat) :
    Contains (intersectInterval a b) x ↔ a.Contains x ∧ b.Contains x := by
  simp only [intersectInterval, Interval.Contains, max_def, min_def]
  split_ifs <;> simp_all [Contains, Interval.Contains] <;> omega

theorem intersectInterval_valid (a b : Interval) : Valid (intersectInterval a b) := by
  simp only [intersectInterval]
  split_ifs <;> simp_all [Valid, Interval.Valid]

def differenceInterval (a b : Interval) : List Interval :=
  if b.high < a.low ∨ a.high < b.low then [a] else
  (if a.low < b.low then [⟨a.low, b.low - 1⟩] else []) ++
  (if b.high < a.high then [⟨b.high + 1, a.high⟩] else [])

theorem differenceInterval_contains (a b : Interval) (_ha : a.Valid) (hb : b.Valid)
    (x : Nat) : Contains (differenceInterval a b) x ↔ a.Contains x ∧ ¬ b.Contains x := by
  simp only [differenceInterval]
  split_ifs <;> simp_all [Contains, Interval.Contains, Interval.Valid] <;> omega

theorem differenceInterval_valid (a b : Interval) (_ha : a.Valid) :
    Valid (differenceInterval a b) := by
  simp only [differenceInterval]
  split_ifs <;> simp_all [Valid, Interval.Valid] <;> omega

def intersection (a b : List Interval) : List Interval :=
  a.flatMap fun left => b.flatMap (intersectInterval left)

theorem intersection_contains (a b : List Interval) (x : Nat) :
    Contains (intersection a b) x ↔ Contains a x ∧ Contains b x := by
  simp only [intersection, contains_flatMap, intersectInterval_contains]
  simp only [Contains]
  aesop

def subtractOne (a : List Interval) (cut : Interval) : List Interval :=
  a.flatMap fun r => differenceInterval r cut

theorem subtractOne_contains (a : List Interval) (cut : Interval)
    (ha : Valid a) (hc : cut.Valid) (x : Nat) :
    Contains (subtractOne a cut) x ↔ Contains a x ∧ ¬ cut.Contains x := by
  simp only [subtractOne, contains_flatMap]
  constructor
  · rintro ⟨r, hr, present⟩
    have result := (differenceInterval_contains r cut (ha r hr) hc x).mp present
    exact ⟨⟨r, hr, result.1⟩, result.2⟩
  · rintro ⟨⟨r, hr, present⟩, absent⟩
    exact ⟨r, hr, (differenceInterval_contains r cut (ha r hr) hc x).mpr ⟨present, absent⟩⟩

theorem subtractOne_valid (a : List Interval) (cut : Interval) (ha : Valid a) :
    Valid (subtractOne a cut) := by
  intro r hr
  obtain ⟨source, hs, hm⟩ := List.mem_flatMap.mp hr
  exact differenceInterval_valid source cut (ha source hs) r hm

def difference (a : List Interval) : List Interval → List Interval
  | [] => a
  | cut :: rest => difference (subtractOne a cut) rest

theorem difference_contains (a b : List Interval) (ha : Valid a) (hb : Valid b)
    (x : Nat) : Contains (difference a b) x ↔ Contains a x ∧ ¬ Contains b x := by
  induction b generalizing a with
  | nil => simp [difference]
  | cons cut rest ih =>
    have hc : cut.Valid := hb cut (by simp)
    have hr : Valid rest := fun r h => hb r (by simp [h])
    rw [difference, ih (subtractOne a cut) (subtractOne_valid a cut ha) hr,
      subtractOne_contains a cut ha hc]
    simp only [contains_cons]
    tauto

theorem difference_valid (a b : List Interval) (ha : Valid a) : Valid (difference a b) := by
  induction b generalizing a with
  | nil => exact ha
  | cons cut rest ih => exact ih (subtractOne a cut) (subtractOne_valid a cut ha)

def complement (domain ranges : List Interval) : List Interval := difference domain ranges

theorem complement_contains (domain ranges : List Interval)
    (hu : Valid domain) (hr : Valid ranges) (x : Nat) :
    Contains (complement domain ranges) x ↔ Contains domain x ∧ ¬ Contains ranges x :=
  difference_contains domain ranges hu hr x

theorem complement_twice (domain ranges : List Interval)
    (hu : Valid domain) (hr : Valid ranges) (x : Nat) :
    Contains (complement domain (complement domain ranges)) x ↔
      Contains domain x ∧ Contains ranges x := by
  rw [complement_contains domain (complement domain ranges) hu
      (difference_valid domain ranges hu), complement_contains domain ranges hu hr]
  tauto

def hull (a b : Interval) : Interval := ⟨min a.low b.low, max a.high b.high⟩

theorem hull_contains (a b : Interval) (_ha : a.Valid) (_hb : b.Valid)
    (nearLeft : a.low ≤ b.high + 1) (nearRight : b.low ≤ a.high + 1) (x : Nat) :
    (hull a b).Contains x ↔ a.Contains x ∨ b.Contains x := by
  simp only [hull, Interval.Contains, min_def, max_def]
  split_ifs <;> simp_all [Interval.Valid] <;> omega

def insert (r : Interval) : List Interval → List Interval
  | [] => [r]
  | head :: rest =>
    if r.high + 1 < head.low then r :: head :: rest else
    if head.high + 1 < r.low then head :: insert r rest else
    insert (hull r head) rest

theorem insert_valid (r : Interval) (rs : List Interval) (hr : r.Valid) (hs : Valid rs) :
    Valid (insert r rs) := by
  induction rs generalizing r with
  | nil => simpa [insert, Valid] using hr
  | cons head rest ih =>
    have hh := hs head (by simp)
    have ht : Valid rest := fun x hx => hs x (by simp [hx])
    have hm : (hull r head).Valid := by
      simp only [hull, Interval.Valid, min_def, max_def]
      split_ifs <;> simp_all [Interval.Valid] <;> omega
    simp only [insert]
    split_ifs
    · simp only [Valid, List.mem_cons]
      intro x hx
      rcases hx with h | h | h
      · subst x; exact hr
      · subst x; exact hh
      · exact ht x h
    · have tail := ih r hr ht
      simp only [Valid, List.mem_cons]
      intro x hx
      rcases hx with h | h
      · subst x; exact hh
      · exact tail x h
    · exact ih (hull r head) hm ht

theorem insert_contains (r : Interval) (rs : List Interval) (hr : r.Valid)
    (hs : Valid rs) (x : Nat) :
    Contains (insert r rs) x ↔ r.Contains x ∨ Contains rs x := by
  induction rs generalizing r with
  | nil => simp [insert, Contains]
  | cons head rest ih =>
    have hh := hs head (by simp)
    have ht : Valid rest := fun y hy => hs y (by simp [hy])
    have hm : (hull r head).Valid := by
      simp only [hull, Interval.Valid, min_def, max_def]
      split_ifs <;> simp_all [Interval.Valid] <;> omega
    simp only [insert]
    split_ifs with before after
    · simp
    · rw [contains_cons, ih r hr ht, contains_cons]
      tauto
    · rw [ih (hull r head) hm ht,
        hull_contains r head hr hh (by omega) (by omega), contains_cons]
      tauto

def normalize : List Interval → List Interval
  | [] => []
  | r :: rest => insert r (normalize rest)

theorem normalize_valid (rs : List Interval) (h : Valid rs) : Valid (normalize rs) := by
  induction rs with
  | nil => simp [normalize, Valid]
  | cons r rest ih =>
    exact insert_valid r (normalize rest) (h r (by simp))
      (ih fun x hx => h x (by simp [hx]))

theorem normalize_contains (rs : List Interval) (h : Valid rs) (x : Nat) :
    Contains (normalize rs) x ↔ Contains rs x := by
  induction rs with
  | nil => simp [normalize]
  | cons r rest ih =>
    have tail : Valid rest := fun y hy => h y (by simp [hy])
    rw [normalize, insert_contains r (normalize rest) (h r (by simp))
      (normalize_valid rest tail), ih tail, contains_cons]

def codePoints : List Interval := [⟨0, 0x10ffff⟩]
def scalars : List Interval := [⟨0, 0xd7ff⟩, ⟨0xe000, 0x10ffff⟩]

theorem scalar_membership (x : Nat) :
    Contains scalars x ↔ x ≤ 0x10ffff ∧ ¬ (0xd800 ≤ x ∧ x ≤ 0xdfff) := by
  simp [scalars, Contains, Interval.Contains]
  omega

example : Contains codePoints 0xd800 ∧ ¬ Contains scalars 0xd800 := by
  simp [codePoints, scalars, Contains, Interval.Contains]

example : Contains (normalize [⟨8, 12⟩, ⟨0, 3⟩, ⟨3, 8⟩]) 11 := by
  simp [normalize, insert, hull, Contains, Interval.Contains]

example : ¬ Contains (difference [⟨0, 9⟩] [⟨3, 6⟩]) 4 ∧
    Contains (difference [⟨0, 9⟩] [⟨3, 6⟩]) 8 := by
  simp [difference, subtractOne, differenceInterval, Contains, Interval.Contains]

end Mettapedia.Computability.RegularLanguages.IntervalClasses
