import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits
import Mettapedia.Algebra.Collections.Rest

/-!
# Occurrences, bags and sets, and matching a bag pattern with a witness

A space holds **occurrences**: each has an identity and a label (`OccurrenceCommits.Commits`). If
the identities are forgotten and the labels kept with their counts, the result is a **bag**
(`labels`). If the counts are forgotten too, the result is a **set** (`Finset.image`).

## The two forgetful maps

* `labels_eq_iff_fibers`: two stores have one bag exactly when every label is carried by equally
  many occurrences in each. The identities say only which copy is which.
* `toFinset_labels`: the set of a store is the image of its labels.
* `labels_nodup_iff`: a store's bag repeats no label exactly when the label is injective on the
  store. A set space is such a store. There an occurrence is named by its label, and keeping an
  occurrence is encoded by a predicate query of its label
  (`OccurrenceCommits.encodes_keepAsQuery`). With a repeated label it is not
  (`OccurrenceCommits.not_encodes_keep`): keep needs identities exactly when labels repeat.

## Matching a bag pattern

A bag pattern with named elements and a rest, `{t₁ … tₖ | rest}`, matches a bag modulo
associativity and commutativity when `{t₁ … tₖ} + rest` is the bag, and the rest is then the
difference (`Collections.Rest.bag_rest_iff`). Over a store, a **witness** (`Witness`) is the list of
the occurrences the named elements picked: distinct occurrences of the store carrying the named
labels in order.

* `exists_witness_iff`: a match exists exactly when a witness does, and the rest is the bag of the
  occurrences the witness did not pick (`rest_of_witness`, `match_iff_witness`).
* `check_iff`: `check` decides whether a list is a witness, in one pass over it: for each element,
  one membership test in the store, one in the set of picks so far, and one label comparison.
* `patterns_iff_witness`: with element patterns (each a predicate on labels, such as "matches
  `(edge $x b)` under the substitution found so far"), a match modulo AC exists exactly when some
  list of distinct occurrences satisfies the patterns one by one. Checking a supplied list is one
  pattern match per element. Finding one is NP-complete when the pattern is part of the input
  (matching modulo AC: Benanav, Kapur and Narendran, 1987); for a fixed pattern of `k` elements
  it is a search over at most `n ^ k` lists.
* Sets: a set pattern's elements may pick one occurrence twice (idempotence), so its witness need
  not be duplicate-free (`set_witness_iff`); `Collections.Rest.card_setRests` counts its rests.

## Controls

Two occurrences of one label give two witnesses of one bag match (`Controls.two_witnesses`) and
one bag answer; a third copy is not there (`Controls.counts_refused`); one occurrence picked twice
is refused for bags (`Controls.repeat_refused`) and allowed for sets (`Controls.set_repeat`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ValuesAndLocations.Occurrences

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} {R : Type v} [DecidableEq O]

/-! ## Forgetting identities, then counts -/

omit [DecidableEq O] in
/-- **One bag exactly when every label has equally many occurrences.** -/
theorem labels_eq_iff_fibers [DecidableEq R] (label : O → R) (X Y : Finset O) :
    labels label X = labels label Y ↔
      ∀ r, (X.filter fun o => label o = r).card = (Y.filter fun o => label o = r).card := by
  rw [Multiset.ext]
  simp only [labels, Multiset.count_map, Finset.card_def, Finset.filter_val]
  constructor
  · intro h r
    have := h r
    simpa only [eq_comm] using this
  · intro h r
    have := h r
    simpa only [eq_comm] using this

omit [DecidableEq O] in
/-- **The set of a store is the image of its labels.** -/
theorem toFinset_labels [DecidableEq R] (label : O → R) (X : Finset O) :
    (labels label X).toFinset = X.image label := rfl

omit [DecidableEq O] in
/-- **A store's bag repeats no label exactly when the label is injective on the store.** -/
theorem labels_nodup_iff (label : O → R) (X : Finset O) :
    (labels label X).Nodup ↔ ∀ x ∈ X, ∀ y ∈ X, label x = label y → x = y :=
  Multiset.nodup_map_iff_inj_on X.nodup

/-! ## Witnesses -/

/-- **A witness** that the named labels `ts` are matched in the store `X`: distinct occurrences of
`X` carrying them, in order. -/
structure Witness (label : O → R) (X : Finset O) (ts : List R) (w : List O) : Prop where
  nodup : w.Nodup
  inStore : ∀ o ∈ w, o ∈ X
  labels_eq : w.map label = ts

omit [DecidableEq O] in
/-- A witness gives a sub-bag. -/
theorem le_of_witness {label : O → R} {X : Finset O} {ts : List R} {w : List O}
    (wit : Witness label X ts w) : (ts : Multiset R) ≤ labels label X := by
  rw [← wit.labels_eq, ← Multiset.map_coe]
  exact Multiset.map_le_map ((Multiset.le_iff_subset (Multiset.coe_nodup.mpr wit.nodup)).mpr
    fun o member => wit.inStore o member)

/-- A sub-bag gives a witness. -/
theorem witness_of_le [DecidableEq R] {label : O → R} :
    ∀ (ts : List R) {X : Finset O}, (ts : Multiset R) ≤ labels label X →
      ∃ w, Witness label X ts w
  | [], _, _ => ⟨[], ⟨List.nodup_nil, by simp, rfl⟩⟩
  | t :: ts, X, le => by
      rw [← Multiset.cons_coe] at le
      have mem : t ∈ labels label X := Multiset.mem_of_le le (Multiset.mem_cons_self t _)
      obtain ⟨o, inX, ho⟩ : ∃ o ∈ X, label o = t := by
        simpa [labels] using mem
      have le' : (ts : Multiset R) ≤ labels label (X.erase o) := by
        have erased : labels label (X.erase o) = (labels label X).erase t := by
          unfold labels
          rw [Finset.erase_val, Multiset.map_erase_of_mem label X.val (Finset.mem_val.mpr inX), ho]
        rw [erased]
        have := Multiset.erase_le_erase t le
        rwa [Multiset.erase_cons_head] at this
      obtain ⟨w, wit⟩ := witness_of_le ts le'
      refine ⟨o :: w, ⟨List.nodup_cons.mpr ⟨fun inW => ?_, wit.nodup⟩, fun x member => ?_, ?_⟩⟩
      · exact Finset.notMem_erase o X (wit.inStore o inW)
      · rcases List.mem_cons.mp member with rfl | inW
        · exact inX
        · exact Finset.mem_of_mem_erase (wit.inStore x inW)
      · simp [ho, wit.labels_eq]

/-- **A match modulo AC exists exactly when a witness does.** -/
theorem exists_witness_iff [DecidableEq R] (label : O → R) (X : Finset O) (ts : List R) :
    (∃ w, Witness label X ts w) ↔ (ts : Multiset R) ≤ labels label X :=
  ⟨fun ⟨_, wit⟩ => le_of_witness wit, witness_of_le ts⟩

/-- **The rest is the bag of what the witness did not pick.** -/
theorem rest_of_witness [DecidableEq R] {label : O → R} {X : Finset O} {ts : List R} {w : List O}
    (wit : Witness label X ts w) : labels label (X \ w.toFinset) = labels label X - ts := by
  have sub : w.toFinset ⊆ X := fun o member => wit.inStore o (List.mem_toFinset.mp member)
  rw [labels_sdiff_of_subset label sub]
  congr 1
  unfold labels
  rw [List.toFinset_val, List.dedup_eq_self.mpr wit.nodup, Multiset.map_coe, wit.labels_eq]

/-- **A bag pattern with a rest matches exactly when a witness exists**, and its rest is then the
labels the witness did not pick. -/
theorem match_iff_witness [DecidableEq R] (label : O → R) (X : Finset O) (ts : List R) :
    (∃ rest, (ts : Multiset R) + rest = labels label X) ↔ ∃ w, Witness label X ts w := by
  rw [exists_witness_iff]
  constructor
  · rintro ⟨rest, eq⟩
    exact ((Mettapedia.Algebra.Collections.Rest.bag_rest_iff _ rest _).mp eq).1
  · intro le
    exact ⟨_, (Mettapedia.Algebra.Collections.Rest.bag_rest_iff _ _ _).mpr ⟨le, rfl⟩⟩

/-! ## Checking a witness in one pass -/

/-- **One pass over a proposed witness**: each picked occurrence is in the store, was not picked
before, and carries its named label. -/
def check [DecidableEq R] (label : O → R) (X : Finset O) : List O → List R → Finset O → Bool
  | [], [], _ => true
  | o :: w, t :: ts, seen =>
      (decide (o ∈ X) && decide (o ∉ seen) && decide (label o = t)) &&
        check label X w ts (insert o seen)
  | _, _, _ => false

theorem check_iff [DecidableEq R] (label : O → R) (X : Finset O) :
    ∀ (w : List O) (ts : List R) (seen : Finset O),
      check label X w ts seen = true ↔
        w.Nodup ∧ (∀ o ∈ w, o ∈ X ∧ o ∉ seen) ∧ w.map label = ts
  | [], [], _ => by simp [check]
  | [], _ :: _, _ => by simp [check]
  | _ :: _, [], _ => by simp [check]
  | o :: w, t :: ts, seen => by
      have ih := check_iff label X w ts (insert o seen)
      simp only [check, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih]
      constructor
      · rintro ⟨⟨⟨inX, notSeen⟩, labelled⟩, nodup, rest, mapped⟩
        refine ⟨List.nodup_cons.mpr ⟨fun inW => (rest o inW).2 (Finset.mem_insert_self o seen),
          nodup⟩, fun x member => ?_, by simp [labelled, mapped]⟩
        rcases List.mem_cons.mp member with rfl | inW
        · exact ⟨inX, notSeen⟩
        · exact ⟨(rest x inW).1, fun s => (rest x inW).2 (Finset.mem_insert_of_mem s)⟩
      · rintro ⟨nodup, inStore, mapped⟩
        obtain ⟨notInW, nodup'⟩ := List.nodup_cons.mp nodup
        have head := inStore o List.mem_cons_self
        simp only [List.map_cons, List.cons.injEq] at mapped
        refine ⟨⟨head, mapped.1⟩, nodup', fun x member =>
          ⟨(inStore x (List.mem_cons_of_mem _ member)).1, ?_⟩, mapped.2⟩
        rw [Finset.mem_insert]
        rintro (rfl | s)
        · exact notInW member
        · exact (inStore x (List.mem_cons_of_mem _ member)).2 s

/-- **`check` decides witnesses.** -/
theorem check_empty_iff [DecidableEq R] (label : O → R) (X : Finset O) (w : List O) (ts : List R) :
    check label X w ts ∅ = true ↔ Witness label X ts w := by
  rw [check_iff]
  constructor
  · rintro ⟨nodup, inStore, mapped⟩
    exact ⟨nodup, fun o member => (inStore o member).1, mapped⟩
  · rintro ⟨nodup, inStore, mapped⟩
    exact ⟨nodup, fun o member => ⟨inStore o member, Finset.notMem_empty o⟩, mapped⟩

/-! ## Element patterns -/

/-- **Matching element patterns modulo AC is choosing distinct occurrences that satisfy them one by
one.** -/
theorem patterns_iff_witness [DecidableEq R] (label : O → R) (X : Finset O) (ps : List (R → Prop)) :
    (∃ ts : List R, List.Forall₂ (fun p t => p t) ps ts ∧ (ts : Multiset R) ≤ labels label X) ↔
      ∃ w : List O, w.Nodup ∧ (∀ o ∈ w, o ∈ X) ∧ List.Forall₂ (fun p o => p (label o)) ps w := by
  constructor
  · rintro ⟨ts, sat, le⟩
    obtain ⟨w, wit⟩ := witness_of_le ts le
    refine ⟨w, wit.nodup, wit.inStore, ?_⟩
    rw [← wit.labels_eq] at sat
    exact List.forall₂_map_right_iff.mp sat
  · rintro ⟨w, nodup, inStore, sat⟩
    exact ⟨w.map label, List.forall₂_map_right_iff.mpr sat,
      le_of_witness ⟨nodup, inStore, rfl⟩⟩

/-! ## Sets -/

omit [DecidableEq O] in
/-- **A set pattern's elements may share an occurrence**: a set match is a list of occurrences of
the store carrying the named labels, repeats allowed. -/
theorem set_witness_iff [DecidableEq R] (label : O → R) (X : Finset O) :
    ∀ ts : List R, ts.toFinset ⊆ X.image label ↔ ∃ w : List O, (∀ o ∈ w, o ∈ X) ∧ w.map label = ts
  | [] => by simp
  | t :: ts => by
      constructor
      · intro sub
        have head : t ∈ X.image label := sub (List.mem_toFinset.mpr List.mem_cons_self)
        obtain ⟨o, inX, ho⟩ := Finset.mem_image.mp head
        have tail : ts.toFinset ⊆ X.image label := fun r member =>
          sub (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp member)))
        obtain ⟨w, inStore, mapped⟩ := (set_witness_iff label X ts).mp tail
        refine ⟨o :: w, fun x member => ?_, by simp [ho, mapped]⟩
        rcases List.mem_cons.mp member with rfl | inW
        · exact inX
        · exact inStore x inW
      · rintro ⟨w, inStore, mapped⟩ r member
        rw [List.mem_toFinset, ← mapped] at member
        obtain ⟨o, inW, rfl⟩ := List.mem_map.mp member
        exact Finset.mem_image_of_mem label (inStore o inW)

/-! ## Controls -/

namespace Controls

/-- Every occurrence carries `a`. -/
def same : ℕ → Char := fun _ => 'a'

/-- **Two witnesses of one bag match**: in `{0, 1}`, both labelled `a`, the pattern `{a | rest}`
picks `0` or `1`; the bag answer is one. -/
theorem two_witnesses :
    check same {0, 1} [0] ['a'] ∅ = true ∧ check same {0, 1} [1] ['a'] ∅ = true ∧
      labels same ({0, 1} \ [0].toFinset) = labels same ({0, 1} \ [1].toFinset) := by
  decide

/-- **Counts are seen**: `{a a a}` is not in a store with two `a`s. -/
theorem counts_refused : ¬ ((['a', 'a', 'a'] : List Char) : Multiset Char) ≤ labels same {0, 1} := by
  decide

/-- **One occurrence is not picked twice in a bag match.** -/
theorem repeat_refused : check same {0, 1} [0, 0] ['a', 'a'] ∅ = false := by decide

/-- **In a set match it may be**: one occurrence of `a` meets the pattern `{a a}`, and the bag match
does not exist. -/
theorem set_repeat :
    (['a', 'a'] : List Char).toFinset ⊆ ({0} : Finset ℕ).image same ∧
      ¬ ((['a', 'a'] : List Char) : Multiset Char) ≤ labels same {0} := by
  decide

/-- **Identities by labels**: under an injective label the bag of a store repeats nothing; under
`same` it does. -/
theorem nodup_controls :
    (labels (id : ℕ → ℕ) {0, 1}).Nodup ∧ ¬ (labels same {0, 1}).Nodup := by
  decide

end Controls

end Mettapedia.SetTheory.ValuesAndLocations.Occurrences
