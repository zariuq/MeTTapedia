import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Basic

/-!
# Seeds: allocating fresh names by position

The encoding allocates a name for each position in the source term.  Doing
that by quoting the subterm a name must be fresh for makes every allocated
name carry a copy of that subterm, and the output grows quadratically before
anything else is counted.  Seeds avoid this: one fresh name, then two
injective constructors with disjoint images, give a distinct name for every
binary string at a cost of the seed plus the string.

## What is proved

* `components` — the parallel components of a term, with parallel composition
  flattened and units discarded.  This is the normal form for the monoid laws,
  and `cong_components` shows structural congruence preserves it, which is
  what lets congruence be ruled out rather than merely equality.
* `names_size_lt` — every name of a term is the quotation of a proper subterm,
  hence strictly smaller.
* `self_not_mem_names` — consequently no term is among its own names, so a
  term's own quotation is a seed for it.
* `seedAt` with `seedAt_injective` — distinct strings allocate distinct names,
  because the two constructors are injective with disjoint images.
* `seedAt_not_mem_names` — every name allocated from a term is fresh for it,
  by size.
* `seedAt_cong_injective` — and distinct allocations are distinct *up to
  structural congruence*, not merely syntactically.  This is the form the
  encoding needs, since subjects are matched up to name equivalence.

The congruence-closed distinctness is where `components` earns its place: an
allocated name at a nonempty string is a single atom, so its components are a
singleton, and congruent singletons have equal members.

## Scope

`seedAt_cong_injective` is stated for nonempty allocating strings, which is
what allocation by position uses; the seed itself is covered separately by
`seedAt_not_mem_names`, which is the freshness the encoding actually requires
of it.

## References

- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026, whose seed discipline and freshness lemma these follow.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-- The parallel components of a term: parallel composition flattened and
units discarded.  This is the normal form for the monoid laws. -/
def components : Comb → Multiset Comb
  | nil => 0
  | par p q => components p + components q
  | mm a b => {mm a b}
  | dd a b c => {dd a b c}
  | kk a => {kk a}
  | fw a b => {fw a b}
  | bl a b => {bl a b}
  | br a b => {br a b}
  | sy a b c => {sy a b c}
  | ev a => {ev a}
  | qq a p => {qq a p}
  | consPar a b c => {consPar a b c}
  | consMsg a b c => {consMsg a b c}
  | consDup a b c e => {consDup a b c e}
  | consSyn a b c e => {consSyn a b c e}

/-- Structural congruence is exactly equality of parallel components on the
generators: it preserves them. -/
theorem cong_components {p q : Comb} (h : Cong p q) :
    components p = components q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => simp [components]
  | parComm p q => simp only [components]; exact add_comm _ _
  | parAssoc p q r => simp only [components]; exact add_assoc _ _ _
  | parLeft q _ ih => simp only [components, ih]
  | parRight p _ ih => simp only [components, ih]

/-- Term size. -/
def size : Comb → ℕ
  | nil => 1
  | par p q => 1 + size p + size q
  | mm a b => 1 + size a + size b
  | dd a b c => 1 + size a + size b + size c
  | kk a => 1 + size a
  | fw a b => 1 + size a + size b
  | bl a b => 1 + size a + size b
  | br a b => 1 + size a + size b
  | sy a b c => 1 + size a + size b + size c
  | ev a => 1 + size a
  | qq a p => 1 + size a + size p
  | consPar a b c => 1 + size a + size b + size c
  | consMsg a b c => 1 + size a + size b + size c
  | consDup a b c e => 1 + size a + size b + size c + size e
  | consSyn a b c e => 1 + size a + size b + size c + size e

/-- Every name of a term is the quotation of a proper subterm, hence smaller
than the term itself. -/
theorem names_size_lt : ∀ (t x : Comb), x ∈ names t → size x < size t := by
  intro t
  induction t with
  | nil => intro x hx; simp [names] at hx
  | par p q ihp ihq =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      rcases hx with h | h
      · have := ihp x h; simp only [size]; omega
      · have := ihq x h; simp only [size]; omega
  | mm a b iha ihb =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (h | h) | h
      · rcases h with h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
  | dd a b c iha ihb ihc =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with ((h | h) | h) | h
      · rcases h with h | h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
      · have := ihc x h; omega
  | kk a iha =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with h | h
      · subst h; omega
      · have := iha x h; omega
  | fw a b iha ihb =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (h | h) | h
      · rcases h with h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
  | bl a b iha ihb =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (h | h) | h
      · rcases h with h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
  | br a b iha ihb =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (h | h) | h
      · rcases h with h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
  | sy a b c iha ihb ihc =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with ((h | h) | h) | h
      · rcases h with h | h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
      · have := ihc x h; omega
  | ev a iha =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with h | h
      · subst h; omega
      · have := iha x h; omega
  | qq a p iha ihp =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (h | h) | h
      · rcases h with h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihp x h; omega
  | consPar a b c iha ihb ihc =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with ((h | h) | h) | h
      · rcases h with h | h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
      · have := ihc x h; omega
  | consMsg a b c iha ihb ihc =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with ((h | h) | h) | h
      · rcases h with h | h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
      · have := ihc x h; omega
  | consDup a b c e iha ihb ihc ihe =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (((h | h) | h) | h) | h
      · rcases h with h | h | h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
      · have := ihc x h; omega
      · have := ihe x h; omega
  | consSyn a b c e iha ihb ihc ihe =>
      intro x hx
      simp only [names, Set.mem_union] at hx
      simp only [size]
      rcases hx with (((h | h) | h) | h) | h
      · rcases h with h | h | h | h <;> subst h <;> omega
      · have := iha x h; omega
      · have := ihb x h; omega
      · have := ihc x h; omega
      · have := ihe x h; omega

/-- **A term's own quotation is a seed for it.**  No term is among its own
names. -/
theorem self_not_mem_names (t : Comb) : t ∉ names t := by
  intro h
  exact absurd (names_size_lt t t h) (lt_irrefl _)

/-! ## Seed extension -/

/-- Seed extension.  Two injective constructors with disjoint images allocate
a distinct name for each binary string, so names can be allocated by position
without quoting the subterm they must be fresh for. -/
def seedAt (s : Comb) : List Bool → Comb
  | [] => s
  | false :: w => mm (seedAt s w) nil
  | true :: w => kk (seedAt s w)

theorem size_le_seedAt (s : Comb) : ∀ w : List Bool, size s ≤ size (seedAt s w)
  | [] => le_refl _
  | false :: w => by
      have := size_le_seedAt s w
      simp only [seedAt, size]
      omega
  | true :: w => by
      have := size_le_seedAt s w
      simp only [seedAt, size]
      omega

theorem size_lt_seedAt_cons (s : Comb) (b : Bool) (w : List Bool) :
    size (seedAt s w) < size (seedAt s (b :: w)) := by
  cases b <;> simp only [seedAt, size] <;> omega

/-- Seed extension is injective in the allocating string. -/
theorem seedAt_injective (s : Comb) :
    ∀ {w w' : List Bool}, seedAt s w = seedAt s w' → w = w' := by
  intro w
  induction w with
  | nil =>
      intro w' h
      cases w' with
      | nil => rfl
      | cons b v =>
          exfalso
          have low := size_le_seedAt s v
          have high := size_lt_seedAt_cons s b v
          simp only [seedAt] at h
          rw [← h] at high
          omega
  | cons b v ih =>
      intro w' h
      cases w' with
      | nil =>
          exfalso
          have low := size_le_seedAt s v
          have high := size_lt_seedAt_cons s b v
          simp only [seedAt] at h
          rw [h] at high
          omega
      | cons b' v' =>
          cases b <;> cases b' <;> simp only [seedAt] at h
          · exact congrArg _ (ih (by injection h))
          · exact Comb.noConfusion h
          · exact Comb.noConfusion h
          · exact congrArg _ (ih (by injection h))

/-- Seeds allocated from a term are fresh for it. -/
theorem seedAt_not_mem_names (t : Comb) (w : List Bool) :
    seedAt t w ∉ names t := by
  intro h
  have small := names_size_lt t _ h
  have large := size_le_seedAt t w
  omega

/-- Allocated seeds are pairwise distinct up to structural congruence. -/
theorem seedAt_cong_injective (s : Comb) {w w' : List Bool}
    (hw : w ≠ []) (hw' : w' ≠ []) (h : Cong (seedAt s w) (seedAt s w')) :
    w = w' := by
  obtain ⟨b, v, rfl⟩ : ∃ b v, w = b :: v := by
    cases w with
    | nil => exact absurd rfl hw
    | cons b v => exact ⟨b, v, rfl⟩
  obtain ⟨b', v', rfl⟩ : ∃ b' v', w' = b' :: v' := by
    cases w' with
    | nil => exact absurd rfl hw'
    | cons b' v' => exact ⟨b', v', rfl⟩
  have comp := cong_components h
  refine seedAt_injective s ?_
  cases b <;> cases b' <;>
    simp only [seedAt, components, Multiset.singleton_inj] at comp <;>
    simp only [seedAt] <;> exact comp

/-! ## Allocation by a counter

A compiler does not want to choose seed strings; it wants a counter.  `slot`
turns a natural number into a seed position, so every freshness side condition a
translation incurs is discharged by an inequality between numbers.
-/

/-- The allocating string for slot `n`: `n` ones followed by a zero. -/
def slotString (n : ℕ) : List Bool := List.replicate n true ++ [false]

theorem slotString_ne_nil (n : ℕ) : slotString n ≠ [] := by
  simp [slotString]

theorem slotString_injective {m n : ℕ} (h : slotString m = slotString n) : m = n := by
  have hlen := congrArg List.length h
  simpa [slotString] using hlen

/-- The `n`-th name allocated from a seed. -/
def slot (s : Comb) (n : ℕ) : Comb := seedAt s (slotString n)

/-- Distinct slots are distinct names. -/
theorem slot_ne {s : Comb} {m n : ℕ} (h : m ≠ n) : slot s m ≠ slot s n :=
  fun heq => h (slotString_injective (seedAt_injective s heq))

/-- Distinct slots are distinct names up to structural congruence, which is the
form a freshness side condition on a reduction takes. -/
theorem slot_not_cong {s : Comb} {m n : ℕ} (h : m ≠ n) :
    ¬ Cong (slot s m) (slot s n) :=
  fun hcong => h (slotString_injective
    (seedAt_cong_injective s (slotString_ne_nil m) (slotString_ne_nil n) hcong))

theorem slot_injective (s : Comb) : Function.Injective (slot s) := by
  intro m n h
  by_contra hne
  exact slot_ne hne h

/-- The seed base is never one of its own slots, so a term may safely be used as
the input name of a soup wired from its own slots. -/
theorem ne_slot_self (s : Comb) (n : ℕ) : s ≠ slot s n := by
  intro h
  exact slotString_ne_nil n
    (seedAt_injective s (show seedAt s [] = seedAt s (slotString n) from h)).symm

/-- Every allocated slot is fresh for the term it was allocated from. -/
theorem slot_not_mem_names (s : Comb) (n : ℕ) : slot s n ∉ names s :=
  seedAt_not_mem_names s (slotString n)

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.cong_components
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.names_size_lt
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.self_not_mem_names
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.seedAt_injective
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.seedAt_not_mem_names
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.seedAt_cong_injective
