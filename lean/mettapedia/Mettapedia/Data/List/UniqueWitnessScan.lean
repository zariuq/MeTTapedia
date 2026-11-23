import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Unique witnesses: stop on ambiguity, not on the first match

The scanner returns a witness only when there is exactly one matching
occurrence. Identical values in different list positions count separately.
In the finite opaque-input model, a stable read certificate must have
seen two matches or read the whole domain. A maintained index has extra
information and is not subject to that fresh-read lower bound; after a
deletion, however, a count saturated at two cannot maintain itself.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.UniqueWitnessScan

inductive Result (Item : Type*) where
  | none
  | one (item : Item)
  | many
  deriving DecidableEq, Repr

variable {Item : Type*}

def classify : List Item → Result Item
  | [] => .none
  | [item] => .one item
  | _ :: _ :: _ => .many

/-- The second component counts predicate observations. -/
def scan (accept : Item → Bool) (seen : Option Item) :
    List Item → Result Item × Nat
  | [] => (classify seen.toList, 0)
  | item :: rest =>
      if accept item then
        match seen with
        | some _ => (.many, 1)
        | none =>
            let next := scan accept (some item) rest
            (next.1, next.2 + 1)
      else
        let next := scan accept seen rest
        (next.1, next.2 + 1)

/-- The reference first retains every matching occurrence, then classifies
the full list; the scanner does not need to build that list. -/
theorem scan_refines (accept : Item → Bool) (seen : Option Item) (items : List Item) :
    (scan accept seen items).1 = classify (seen.toList ++ items.filter accept) := by
  induction items generalizing seen with
  | nil => simp [scan]
  | cons item rest ih =>
      cases tested : accept item <;> cases seen <;>
        simp [scan, tested, classify, ih]

theorem work_le_length (accept : Item → Bool) (seen : Option Item) (items : List Item) :
    (scan accept seen items).2 ≤ items.length := by
  induction items generalizing seen with
  | nil => simp [scan]
  | cons item rest ih =>
      cases tested : accept item <;> cases seen <;>
        simp [scan, tested, ih]

theorem work_eq_length_if_not_many (accept : Item → Bool) (seen : Option Item)
    (items : List Item) (notMany : (scan accept seen items).1 ≠ .many) :
    (scan accept seen items).2 = items.length := by
  induction items generalizing seen with
  | nil => simp [scan]
  | cons item rest ih =>
      cases tested : accept item <;> cases seen <;>
        simp_all [scan]

/-- No answer or work depends on the suffix left unvisited. -/
theorem scan_observed_prefix (accept : Item → Bool) (seen : Option Item) (items : List Item) :
    scan accept seen (items.take (scan accept seen items).2) = scan accept seen items := by
  induction items generalizing seen with
  | nil => simp [scan]
  | cons item rest ih =>
      cases tested : accept item <;> cases seen <;> simp [scan, tested, ih]

private theorem classify_many_iff (items : List Item) :
    classify items = .many ↔ 2 ≤ items.length := by
  cases items with
  | nil => simp [classify]
  | cons a rest => cases rest <;> simp [classify]

theorem observed_prefix_certifies (accept : Item → Bool) (seen : Option Item)
    (items : List Item) :
    let visits := (scan accept seen items).2
    visits = items.length ∨ 2 ≤ (seen.toList ++ (items.take visits).filter accept).length := by
  dsimp only
  by_cases many : (scan accept seen items).1 = .many
  · right
    have observed := congrArg Prod.fst (scan_observed_prefix accept seen items)
    rw [scan_refines] at observed
    exact (classify_many_iff _).mp (observed.trans many)
  · exact Or.inl (work_eq_length_if_not_many accept seen items many)

private theorem work_le_of_two_in_prefix (accept : Item → Bool) (seen : Option Item)
    (items : List Item) (visits : Nat)
    (two : 2 ≤ (seen.toList ++ (items.take visits).filter accept).length) :
    (scan accept seen items).2 ≤ visits := by
  induction items generalizing seen visits with
  | nil => simp [scan]
  | cons item rest ih =>
      cases visits with
      | zero => cases seen <;> simp at two
      | succ n =>
          cases tested : accept item with
          | false =>
              have shorter := ih seen n (by simpa [tested] using two)
              simpa [scan, tested, Nat.succ_eq_add_one] using Nat.succ_le_succ shorter
          | true =>
              cases seen with
              | none =>
                  have shorter := ih (some item) n (by simpa [tested] using two)
                  simpa [scan, tested, Nat.succ_eq_add_one] using Nat.succ_le_succ shorter
              | some prior => simp [scan, tested]

/-- A prefix scanner cannot stop at a smaller certifying prefix. Together
with `observed_prefix_certifies`, this is an attained work bound, not a
worst-case upper bound in isolation. -/
theorem scan_shortest_certifying_prefix (accept : Item → Bool) (seen : Option Item)
    (items : List Item) (visits : Nat)
    (certified : visits = items.length ∨
      2 ≤ (seen.toList ++ (items.take visits).filter accept).length) :
    (scan accept seen items).2 ≤ visits := by
  rcases certified with same | two
  · rw [same]
    exact work_le_length accept seen items
  · exact work_le_of_two_in_prefix accept seen items visits two

section Certificate

variable {Position : Type*} [DecidableEq Position]

/-- Reads observe membership at named occurrence positions. A certificate
must give the same answer for every completion of the unread positions. -/
def CertifiesUnique (domain tested hits : Finset Position) : Prop :=
  ∀ other ⊆ domain, other ∩ tested = hits ∩ tested →
    (other.card = 1 ↔ hits.card = 1)

/-- Sharp certificate bound for the unique-witness decision, even allowing
random-access tests. Until ambiguity is witnessed, an unread position can
always change the decision for some completion. -/
theorem certifiesUnique_iff (domain tested hits : Finset Position)
    (inside : tested ⊆ domain) (hitsInside : hits ⊆ domain) :
    CertifiesUnique domain tested hits ↔ tested = domain ∨ 2 ≤ (hits ∩ tested).card := by
  constructor
  · intro certificate
    by_cases all : tested = domain
    · exact Or.inl all
    · apply Or.inr
      by_contra fewer
      have lacks : ¬ domain ⊆ tested := fun included => all (Finset.Subset.antisymm inside included)
      obtain ⟨hidden, atDomain, unread⟩ := Finset.not_subset.mp lacks
      let known := hits ∩ tested
      have testedKnown : known ⊆ tested := Finset.inter_subset_right
      have first : known ∩ tested = known := Finset.inter_eq_left.mpr testedKnown
      have second : insert hidden known ∩ tested = known := by
        ext a
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | wasRead, mem⟩
          · exact (unread mem).elim
          · exact wasRead
        · intro mem
          exact ⟨Or.inr mem, testedKnown mem⟩
      have noHidden : hidden ∉ known := fun mem => unread (testedKnown mem)
      have includeKnown : known ⊆ domain := testedKnown.trans inside
      have c0 := certificate known includeKnown first
      have c1 := certificate (insert hidden known) (Finset.insert_subset atDomain includeKnown) second
      rw [Finset.card_insert_of_notMem noHidden] at c1
      change ¬ 2 ≤ known.card at fewer
      omega
  · rintro (all | two) other sub equal
    · subst tested
      rw [Finset.inter_eq_left.mpr sub, Finset.inter_eq_left.mpr hitsInside] at equal
      rw [equal]
    · have measured := Finset.card_le_card (Finset.inter_subset_left : hits ∩ tested ⊆ hits)
      have alternatives :=
        Finset.card_le_card (Finset.inter_subset_left : other ∩ tested ⊆ other)
      rw [equal] at alternatives
      omega

end Certificate

def saturatedCount (size : Nat) : Nat := min 2 size

/-- A two-or-more bit is sufficient for observation, not for incremental
deletion. Two and three occurrences have equal summaries before deletion,
and distinguishable summaries afterwards. -/
theorem saturatedCount_not_decrementable :
    ¬ ∃ decrement : Nat → Nat, ∀ n, 0 < n →
      decrement (saturatedCount n) = saturatedCount (n - 1) := by
  rintro ⟨decrement, law⟩
  have two := law 2 (by decide)
  have three := law 3 (by decide)
  norm_num [saturatedCount] at two three
  omega

namespace Controls

theorem duplicates_are_two_occurrences :
    scan (fun _ : Nat => true) none [7, 7, 8, 9] = (.many, 2) := by decide

theorem the_first_hit_is_not_a_unique_certificate :
    scan (· == 7) none [7, 8, 2, 3] = (.one 7, 4) := by decide

end Controls
end Mettapedia.Data.List.UniqueWitnessScan
