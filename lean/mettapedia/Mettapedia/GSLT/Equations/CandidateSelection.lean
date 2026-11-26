import Mettapedia.GSLT.Equations.AtomicMatcher
import Mettapedia.GSLT.Equations.OccurrenceRuns
import Mathlib.Data.List.Dedup

/-! # A cover by selectors, or one generalizing selector

Literal expansions are candidate requests, not separate raw unifications:
putting a raw repeated-variable constraint in a request can miss an atomic
quotient match. Merge only positions from a common ordered occurrence view.
Separate cursors' private offsets are not suitable keys for this operation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.CandidateSelection

open Atomic OccurrenceRuns
open Contracts.ScopedAliasSections (GTerm)

variable {S V C I : Type*}

/-- Test literal positions, treating each variable occurrence as a wildcard.
Identity between variable occurrences is checked by the final matcher. -/
def shapeFits [DecidableEq C] (key : S → C) : Pattern S V → GTerm S → Bool
  | .sym (.inr _), _ => true
  | .sym (.inl s), .sym t => decide (key s = key t)
  | .app p q, .app t u => shapeFits key p t && shapeFits key q u
  | _, _ => false

theorem shapeFits_of_filled [DecidableEq C] (key : S → C) (σ : V → GTerm C)
    (p : Pattern S V) (t : GTerm S) (solution : fill key σ p = rename key t) :
    shapeFits key p t = true := by
  induction p generalizing t with
  | sym s =>
    cases s with
    | inl a => cases t <;> simp_all [fill, rename, shapeFits]
    | inr v => rfl
  | app p q ip iq => cases t <;> simp_all [fill, rename, shapeFits]

theorem shapeFits_of_match [DecidableEq C] [DecidableEq V]
    (key : S → C) (p : Pattern S V) (t : GTerm S) (env : Bindings V S)
    (matched : matchFrom key p t (fun _ => none) = some env) :
    shapeFits key p t = true := by
  have yes : (matchFrom key p t (fun _ => none)).isSome :=
    Option.isSome_iff_exists.mpr ⟨env, matched⟩
  obtain ⟨σ, exactMatch⟩ := (accepts_iff key p t).1 yes
  exact shapeFits_of_filled key σ p t exactMatch

/-- Enumerate selectors by changing only literal spelling. This is useful
when the product of the relevant class sizes is small. -/
def expansions (members : C → List S) (key : S → C) : Pattern S V → List (Pattern S V)
  | .sym (.inr v) => [.sym (.inr v)]
  | .sym (.inl s) => (members (key s)).map fun t => .sym (.inl t)
  | .app p q =>
    (expansions members key p).flatMap fun a => (expansions members key q).map (.app a)

theorem expansions_cover [DecidableEq S] [DecidableEq C] (members : C → List S)
    (key : S → C) (exactClass : ∀ k a, a ∈ members k ↔ key a = k)
    (p : Pattern S V) (t : GTerm S) :
    (∃ q ∈ expansions members key p, shapeFits id q t = true) ↔ shapeFits key p t = true := by
  induction p generalizing t with
  | sym s =>
    cases s with
    | inr v => simp [expansions, shapeFits]
    | inl a =>
      cases t with
      | sym b =>
        simp only [expansions, List.mem_map]
        constructor
        · rintro ⟨_, ⟨s, mem, rfl⟩, selected⟩
          have same : s = b := of_decide_eq_true selected
          subst b
          exact decide_eq_true ((exactClass _ _).1 mem).symm
        · intro selected
          have same : key a = key b := of_decide_eq_true selected
          exact ⟨.sym (.inl b), ⟨b, (exactClass _ _).2 same.symm, rfl⟩, decide_eq_true rfl⟩
      | app _ _ => simp [expansions, shapeFits]
  | app p q ip iq =>
    cases t with
    | sym _ => simp [expansions, shapeFits]
    | app a b =>
      simp only [expansions, List.mem_flatMap, List.mem_map]
      change (∃ w, (∃ pa ∈ expansions members key p,
          ∃ qb ∈ expansions members key q, .app pa qb = w) ∧
          shapeFits id w (.app a b) = true) ↔
        (shapeFits key p a && shapeFits key q b) = true
      rw [Bool.and_eq_true]
      constructor
      · rintro ⟨_, ⟨pa, hm, qb, hn, rfl⟩, ok⟩
        have both : shapeFits id pa a = true ∧ shapeFits id qb b = true := by
          simpa only [shapeFits, Bool.and_eq_true] using ok
        exact ⟨(ip a).1 ⟨pa, hm, both.1⟩, (iq b).1 ⟨qb, hn, both.2⟩⟩
      · rintro ⟨left, right⟩
        obtain ⟨pa, hm, hl⟩ := (ip a).2 left
        obtain ⟨qb, hn, hr⟩ := (iq b).2 right
        exact ⟨.app pa qb, ⟨pa, hm, qb, hn, rfl⟩, by simp [shapeFits, hl, hr]⟩

/-- The actual expansion space is a product, not a sum of alias fanouts. -/
theorem expansion_product (members : C → List S) (key : S → C) (p q : Pattern S V) :
    (expansions members key (.app p q)).length =
      (expansions members key p).length * (expansions members key q).length := by
  simp [expansions, List.length_flatMap]

/-- The single stream case needs no numeric positions. If selection is a
cover, filtering it gives the same occurrence stream as a full scan. -/
theorem filter_covered {Row : Type*} (rows : List Row) (coarse exactMatch : Row → Bool)
    (covers : ∀ r ∈ rows, exactMatch r = true → coarse r = true) :
    (rows.filter coarse).filter exactMatch = rows.filter exactMatch := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro r present
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  exact ⟨fun h => h.1, fun exact => ⟨exact, covers r present exact⟩⟩

section Ordered

variable [LinearOrder I]

/-- Overlapping selector outputs can be unioned once per *occurrence*.
All runs and the final predicate refer to the same ordered view. Every true
match must occur in at least one candidate run; other candidates are allowed.
Equal payloads occupy different positions, so this retains their copies. -/
theorem union_then_filter (store : List I) (sorted : store.SortedLE) (unique : store.Nodup)
    (candidates : List (List I)) (ordered : ∀ xs ∈ candidates, xs.SortedLE)
    (test : I → Bool) (inside : ∀ xs ∈ candidates, ∀ i ∈ xs, i ∈ store)
    (cover : ∀ i ∈ store, test i = true → ∃ xs ∈ candidates, i ∈ xs) :
    (merge candidates).dedup.filter test = store.filter test := by
  have keptSorted : ((merge candidates).dedup.filter test).SortedLE :=
    ((merge_sorted candidates ordered).pairwise.sublist
      (List.dedup_sublist _)).filter test |>.sortedLE
  apply List.Perm.eq_of_sortedLE keptSorted (sorted.pairwise.filter test).sortedLE
  apply (List.perm_ext_iff_of_nodup ((List.nodup_dedup _).filter _)
    (unique.filter _)).mpr
  intro i
  simp only [List.mem_filter, List.mem_dedup, mem_merge]
  constructor
  · rintro ⟨⟨xs, used, found⟩, yes⟩
    exact ⟨inside xs used i found, yes⟩
  · rintro ⟨belongs, yes⟩
    exact ⟨cover i belongs yes, yes⟩

end Ordered

end Mettapedia.GSLT.Equations.CandidateSelection
