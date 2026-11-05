import Mettapedia.Algebra.Collections.Free
import Mettapedia.Algebra.Collections.ObservationalQuotient
import Mathlib.Algebra.Group.End
import Mathlib.Data.List.Sort
import Mathlib.Order.MinMax

/-!
# Folds that cannot see order or multiplicity

The cheap half of the observational-quotient checker: a consumer written as
a right fold, one step per element, respects the reordering of elements
exactly when its step is left-commutative, and also their repetition exactly
when the step is left-idempotent as well. Nothing about the datatype's
constructors enters; the condition is on the observer.

* **Bags, exactly.** A right fold factors through the bag of elements, for
  every initial value, exactly when `step a (step b r) = step b (step a r)`
  (`foldr_factors_bag_iff`). The proof reads the fold as a monoid fold into
  the endomorphisms of the accumulator (`foldr_eq_foldList`), where
  left-commutativity is commutation of the generators, and applies the
  universal property of bags (`Algebra.Collections.foldList_factors_bag_iff`).
* **Sets, exactly.** It factors through the set of elements exactly when the
  step is also left-idempotent, `step a (step a r) = step a r`
  (`foldr_factors_set_iff`).
* **The table of steps.** A step `r ↦ op (e a) r` is left-commutative when
  `op` is commutative and associative (`leftCommutes_of_comm_assoc`), and
  left-idempotent when `op` is also idempotent
  (`leftIdempotent_of_assoc_idem`). A first-match step
  `r ↦ if p a then c else r` is both (`leftCommutes_firstMatch`,
  `leftIdempotent_firstMatch`). So sums, products, counts and maxima, and
  membership tests, are recognized by their operation's own laws.
* **Beyond folds.** A consumer that also reads the rest of the sequence
  respects reordering once it respects one adjacent swap and reordering under
  a common head (`perm_respects_of_swap`): a swap equation conjectured by
  testing becomes a proof by induction on the permutation.
* **The certificate.** For a program that builds sequences by prepending and
  reads them only through such folds, the permutation relation is compatible
  and refines every observer, so storing each sequence as its bag is sound
  (`bag_storage_sound`).

Controls: a find-first step is not left-commutative
(`Controls.findFirst_not_leftCommutes`); counting is left-commutative but not
left-idempotent, so it consumes bags and not sets
(`Controls.count_bag_not_set`); maximum consumes sets (`Controls.max_set`);
subtraction and concatenation are not left-commutative
(`Controls.sub_not_leftCommutes`, `Controls.append_not_leftCommutes`); and a
program that also reads the head of a sequence refutes bag storage
(`Controls.head_refutes_bag_storage`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FoldRespect

open Mettapedia.Algebra.Collections (foldList foldList_factors_bag_iff)
open Mettapedia.Algebra.Collections.ObservationalQuotient

universe u v w

variable {α : Type u} {β : Type v}

/-- The step of a right fold commutes on the left. -/
def LeftCommutes (step : α → β → β) : Prop := ∀ a b r, step a (step b r) = step b (step a r)

/-- The step of a right fold absorbs its own repetition. -/
def LeftIdempotent (step : α → β → β) : Prop := ∀ a r, step a (step a r) = step a r

/-- The steps of a right fold as endomorphisms of the accumulator. -/
def endo (step : α → β → β) (a : α) : Function.End β := step a

/-- A right fold is the monoid fold of its steps, applied to the initial value. -/
theorem foldr_eq_foldList (step : α → β → β) (l : List α) (z : β) :
    l.foldr step z = foldList (endo step) l z := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldr_cons, ih]
      simp only [foldList, List.map_cons, List.prod_cons]
      rfl

theorem commute_endo_iff (step : α → β → β) (a b : α) :
    Commute (endo step a) (endo step b) ↔ ∀ r, step a (step b r) = step b (step a r) := by
  constructor
  · intro h r
    exact congrFun h r
  · intro h
    funext r
    exact h r

/-- **Bags, exactly.** A right fold depends only on the bag of its elements,
for every initial value, exactly when its step is left-commutative. -/
theorem foldr_factors_bag_iff (step : α → β → β) :
    (∃ consume : Multiset α → β → β, ∀ (l : List α) z, l.foldr step z = consume (l : Multiset α) z) ↔
      LeftCommutes step := by
  have lift := foldList_factors_bag_iff (endo step)
  constructor
  · rintro ⟨consume, factors⟩ a b r
    have monoid : ∃ c : Multiset α → Function.End β, ∀ l : List α,
        foldList (endo step) l = c (l : Multiset α) :=
      ⟨consume, fun l => funext fun z => by rw [← foldr_eq_foldList]; exact factors l z⟩
    exact (commute_endo_iff step a b).mp (lift.mp monoid a b) r
  · intro commutes
    obtain ⟨c, factors⟩ := lift.mpr fun a b => (commute_endo_iff step a b).mpr (commutes a b)
    exact ⟨c, fun l z => by rw [foldr_eq_foldList, factors]⟩

/-- With a left-commutative and left-idempotent step, an element already
folded absorbs another copy of itself. -/
theorem foldr_absorb {step : α → β → β} (commutes : LeftCommutes step)
    (idempotent : LeftIdempotent step) {a : α} {l : List α} (member : a ∈ l) (z : β) :
    step a (l.foldr step z) = l.foldr step z := by
  induction l with
  | nil => cases member
  | cons b l ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact idempotent a _
      · rw [List.foldr_cons, commutes a b, ih member]

theorem foldr_dedup [DecidableEq α] {step : α → β → β} (commutes : LeftCommutes step)
    (idempotent : LeftIdempotent step) (l : List α) (z : β) :
    l.dedup.foldr step z = l.foldr step z := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases member : a ∈ l
      · rw [List.dedup_cons_of_mem member, ih, List.foldr_cons,
          foldr_absorb commutes idempotent member]
      · rw [List.dedup_cons_of_notMem member, List.foldr_cons, List.foldr_cons, ih]

/-- **Sets, exactly.** A right fold depends only on the set of its elements,
for every initial value, exactly when its step is left-commutative and
left-idempotent. -/
theorem foldr_factors_set_iff [DecidableEq α] (step : α → β → β) :
    (∃ consume : Finset α → β → β, ∀ (l : List α) z, l.foldr step z = consume l.toFinset z) ↔
      LeftCommutes step ∧ LeftIdempotent step := by
  constructor
  · rintro ⟨consume, factors⟩
    refine ⟨fun a b r => ?_, fun a r => ?_⟩
    · have same : ([a, b] : List α).toFinset = ([b, a] : List α).toFinset := by
        ext x
        simp [or_comm]
      have := factors [a, b] r
      rw [same, ← factors [b, a] r] at this
      simpa using this
    · have same : ([a, a] : List α).toFinset = ([a] : List α).toFinset := by
        ext x
        simp
      have := factors [a, a] r
      rw [same, ← factors [a] r] at this
      simpa using this
  · rintro ⟨commutes, idempotent⟩
    have : LeftCommutative step := ⟨commutes⟩
    refine ⟨fun s z => Multiset.foldr step z s.val, fun l z => ?_⟩
    show l.foldr step z = Multiset.foldr step z l.toFinset.val
    rw [List.toFinset_val, Multiset.coe_foldr, foldr_dedup commutes idempotent]

/-! ## The table of steps -/

/-- A step through a commutative and associative operation commutes on the
left. -/
theorem leftCommutes_of_comm_assoc (op : β → β → β) [Std.Commutative op] [Std.Associative op]
    (e : α → β) : LeftCommutes fun a r => op (e a) r := by
  intro a b r
  show op (e a) (op (e b) r) = op (e b) (op (e a) r)
  rw [← Std.Associative.assoc (op := op), Std.Commutative.comm (op := op) (e a) (e b),
    Std.Associative.assoc (op := op)]

/-- A step through an associative and idempotent operation absorbs
repetition. -/
theorem leftIdempotent_of_assoc_idem (op : β → β → β) [Std.Associative op] [Std.IdempotentOp op]
    (e : α → β) : LeftIdempotent fun a r => op (e a) r := by
  intro a r
  show op (e a) (op (e a) r) = op (e a) r
  rw [← Std.Associative.assoc (op := op), Std.IdempotentOp.idempotent (op := op)]

/-- A first-match step, `c` as soon as some element satisfies `p`. -/
theorem leftCommutes_firstMatch (p : α → Prop) [DecidablePred p] (c : β) :
    LeftCommutes fun a r => if p a then c else r := by
  intro a b r
  by_cases ha : p a <;> by_cases hb : p b <;> simp [ha, hb]

theorem leftIdempotent_firstMatch (p : α → Prop) [DecidablePred p] (c : β) :
    LeftIdempotent fun a r => if p a then c else r := by
  intro a r
  by_cases ha : p a <;> simp [ha]

/-- A step that ignores the element commutes on the left. -/
theorem leftCommutes_blind (f : β → β) : LeftCommutes fun (_ : α) r => f r :=
  fun _ _ _ => rfl

/-! ## Consumers beyond folds -/

/-- **Swap and congruence suffice.** A consumer of sequences respects every
reordering once it respects one adjacent swap at every depth and respects
reordering under a common head; these are the two cases of an induction on
the permutation. A conjectured swap equation, found by testing, is proved by
unfolding the consumer twice; the congruence comes from the induction
hypothesis. -/
theorem perm_respects_of_swap {g : List α → β}
    (swap : ∀ a b l, g (a :: b :: l) = g (b :: a :: l))
    (congr : ∀ a l l', l.Perm l' → g l = g l' → g (a :: l) = g (a :: l')) :
    ∀ {l l' : List α}, l.Perm l' → g l = g l' := by
  intro l l' h
  induction h with
  | nil => rfl
  | cons x p ih => exact congr x _ _ p ih
  | swap x y l => exact swap y x l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A structural recursion that reads the rest only through its own value is
a fold, and its congruence obligation holds by itself. -/
theorem congr_of_fold (step : α → β → β) (z : β) (a : α) (l l' : List α)
    (same : l.foldr step z = l'.foldr step z) :
    (a :: l).foldr step z = (a :: l').foldr step z := by
  rw [List.foldr_cons, List.foldr_cons, same]

/-! ## The certificate for programs that only fold -/

/-- A program that builds sequences by prepending and observes them only by
folds: observer `o` folds with `steps o` from `init o`. -/
def foldMachine {ω : Type w} (steps : ω → α → β → β) (init : ω → β) :
    Machine α ω (List α) β where
  step x l := {x :: l}
  observe o l := l.foldr (steps o) (init o)

variable {ω : Type w} (steps : ω → α → β → β) (init : ω → β)

theorem perm_compatible : (foldMachine steps init).Compatible List.Perm := by
  intro x l l' h
  exact Multiset.Rel.cons (h.cons x) Multiset.Rel.zero

theorem perm_refines (commutes : ∀ o, LeftCommutes (steps o)) :
    (foldMachine steps init).Refines List.Perm := by
  intro o l l' h
  exact h.foldr_eq' (fun x _ y _ z => commutes o y x z) _

/-- **Bag storage is sound for a program that only folds** with
left-commutative steps. -/
theorem bag_storage_sound (commutes : ∀ o, LeftCommutes (steps o)) {l l' : List α}
    (h : l.Perm l') : (foldMachine steps init).Equiv l l' :=
  (perm_compatible steps init).le_equiv _ (perm_refines steps init commutes) h

/-! ## Controls -/

namespace Controls

/-- Return the first nonzero element: `[1, 2]` gives `1`, `[2, 1]` gives `2`. -/
theorem findFirst_not_leftCommutes : ¬ LeftCommutes fun (a r : ℕ) => if a ≠ 0 then a else r := by
  intro h
  have := h 1 2 0
  simp at this

/-- Counting consumes bags and not sets: `[a, a]` and `[a]` have one set of
elements and different counts. -/
theorem count_bag_not_set :
    LeftCommutes (fun (_ : ℕ) (n : ℕ) => n + 1) ∧
      ¬ LeftIdempotent (fun (_ : ℕ) (n : ℕ) => n + 1) := by
  refine ⟨leftCommutes_blind _, fun h => ?_⟩
  have := h 0 0
  simp at this

/-- Maximum consumes sets. -/
theorem max_set : LeftCommutes (fun (a r : ℕ) => max a r) ∧ LeftIdempotent (fun (a r : ℕ) => max a r) :=
  ⟨leftCommutes_of_comm_assoc max id, leftIdempotent_of_assoc_idem max id⟩

theorem sub_not_leftCommutes : ¬ LeftCommutes fun (a r : ℤ) => a - r := by
  intro h
  have : (1 : ℤ) - (2 - 0) = 2 - (1 - 0) := h 1 2 0
  omega

theorem append_not_leftCommutes : ¬ LeftCommutes fun (a r : List ℕ) => a ++ r := by
  intro h
  have := h [1] [2] []
  simp at this

/-- Sorting is the canonical representative of a bag of naturals. -/
def sortNormalizer : Machine.Normalizer (List.Perm (α := ℕ)) where
  nf l := l.insertionSort (· ≤ ·)
  rel_nf l := (List.perm_insertionSort (· ≤ ·) l).symm
  nf_eq l l' h :=
    List.Perm.eq_of_pairwise' (List.pairwise_insertionSort (· ≤ ·) l)
      (List.pairwise_insertionSort (· ≤ ·) l')
      ((List.perm_insertionSort (· ≤ ·) l).trans (h.trans (List.perm_insertionSort (· ≤ ·) l').symm))

/-- A program that sums its sequences and also reads their heads. -/
def sumAndHead : Machine ℕ Bool (List ℕ) ℕ where
  step x l := {x :: l}
  observe
    | true, l => l.foldr (· + ·) 0
    | false, l => l.headD 0

/-- **A head observer refutes bag storage**, although the sum alone would
admit it. -/
theorem head_refutes_bag_storage :
    ¬ ∀ w o l, sumAndHead.answers w o (sortNormalizer.nf l) = sumAndHead.answers w o l :=
  Machine.not_store_sound_of_observer sumAndHead sortNormalizer (a := [2, 1]) (b := [1, 2])
    (List.Perm.swap 1 2 []) false (by decide)

end Controls

end Mettapedia.Algebra.Collections.FoldRespect
