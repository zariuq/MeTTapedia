import Mettapedia.Languages.MeTTa.SpaceKinds
import Mettapedia.Algebra.Collections.SupportObservation
import Mettapedia.Algebra.Collections.Free
import Mathlib.Data.Finset.Dedup

/-!
# Sinks: insertion disciplines fed by a batch of matches

A query that writes its answers into a space inserts a *batch*: the instances of a
template, one per match.  A join enumerates its matches in whatever order the
engine's indexes give, and an engine is free to list one bag of matches in
different orders (`SpaceKindRefinement`).  What reaches the space is the space
kind's insertion discipline applied to the batch, in that order (`insertBatch`).
The kind is then a **sink**, and the question is which kinds are safe sinks for an
unordered join.

* **Order independence is exactly commutation** (`factorsThroughBag_iff`): the
  result depends only on the bag of matches, for every starting state, exactly
  when two insertions commute.
* **Duplicate insensitivity is commutation and idempotence**
  (`factorsThroughSupport_iff`): the result depends only on the set of matches,
  as MM2's support-valued sinks require, exactly when insertions also absorb a
  repeat.  The direction from right to left goes through deduplication
  (`insertBatch_dedup`).

A batch is the list fold
(`Mettapedia.Algebra.Collections.foldList`) for the generator sending an
atom to its insertion, in the opposite monoid of state transformers
(`insertBatch_eq_foldList`, `orderIndependent_iff_commute`).  The bag statement
is then `Algebra.Collections.foldList_factors_bag_iff`; the set statement there assumes a
commutative monoid, while state transformers form a non-commutative one in which
only the generators commute, which is the case proved here.

## The classification of the kinds

| discipline | order independent | duplicate insensitive |
|---|---|---|
| atom (bag) | yes (`atom_orderIndependent`) | no (`Controls.atom_not_idempotent`) |
| set | yes | yes (`set_orderIndependent`, `set_idempotent`) |
| history (queue, stack) | no (`Controls.history_order_dependent`) | no |
| ordered set (`unique-atom`) | no (`Controls.orderedSet_order_dependent`) | yes (`orderedSet_idempotent`) |
| dict, replace or keep the first | no (`Controls.replace_order_dependent`, `Controls.keepFirst_order_dependent`) | yes (`replace_idempotent`, `keepFirst_idempotent`) |
| dict, refuse a second value and keep the dict | no (`Controls.reject_order_dependent`) | yes (`reject_idempotent`) |
| dict, refuse a second value and fail the batch | yes (`conflictPut_orderIndependent`) | yes (`conflictPut_idempotent`) |
| dict, merge by a commutative, associative operation | yes (`merge_orderIndependent`) | exactly for an idempotent operation (`merge_idempotent_iff`; `Controls.mergeAdd_not_idempotent`) |
| removal from a set (MM2's `-` sink) | yes | yes (`setRemove_orderIndependent`, `setRemove_idempotent`) |
| removal of one occurrence from a bag | yes | no (`Controls.atomRemove_not_idempotent`) |

A non-commuting discipline fed by an unordered join exposes the engine's
enumeration order: an insertion-ordered set built from a `match`, a queue filled
from one, a last-writer-wins dict.  Feeding it needs an ordered source or an
explicit tie-breaking order; the alternative is a commuting discipline.  A
refusal is order independent only when it fails the whole batch: the reject
policy of a dict, read as exclusive ownership of each key.  The COO duplicate
policies of the native tensor library (`reject`, `first`, `last`, `sum`,
`combine`) are these dict policies on coordinates: only `reject` as a failure,
`sum`, and a commutative, associative `combine` build one tensor from an
unordered source, and of those only `sum` counts repeats as a bag does.

## MM2's support-valued step

The MORK kernel adds every `+` instance while it enumerates matches and removes
the `-` instances afterwards.  Both disciplines are those of a set, so one firing
is a function of the set of matches (`kernelStep_factorsThroughSupport`); the
order between the two phases is
`Mettapedia.Algebra.LocatedUpdates.removeAfterAdd_eq_addAfterRemove_iff`.
Aggregating sinks that stage their instances in a set and write a function of it
(count, sum, the least `k`) are support observations by construction
(`Mettapedia.Algebra.Collections.SupportObservation.factorsThroughSupport_iff`); a count of
occurrences is not (`Mettapedia.Algebra.Collections.SupportObservation.Controls.use_count_not_support`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceSinks

open Mettapedia.Languages.MeTTa.SpaceKinds
open Mettapedia.Algebra.Collections.SupportObservation

universe u v

variable {α : Type u}

/-! ## Batches -/

/-- Insert a batch of instances, in the order given. -/
def insertBatch (κ : Kind.{u, v} α) (state : κ.State) (batch : List α) : κ.State :=
  batch.foldl κ.add state

/-- Two insertions commute. -/
def OrderIndependent (κ : Kind.{u, v} α) : Prop :=
  ∀ state first second, κ.add (κ.add state first) second = κ.add (κ.add state second) first

/-- Inserting an atom again changes nothing. -/
def Idempotent (κ : Kind.{u, v} α) : Prop :=
  ∀ state atom, κ.add (κ.add state atom) atom = κ.add state atom

@[simp] theorem insertBatch_nil (κ : Kind.{u, v} α) (state : κ.State) :
    insertBatch κ state [] = state :=
  rfl

@[simp] theorem insertBatch_cons (κ : Kind.{u, v} α) (state : κ.State) (atom : α)
    (batch : List α) : insertBatch κ state (atom :: batch) = insertBatch κ (κ.add state atom) batch :=
  rfl

/-- The insertion of an atom, as an element of the opposite monoid of state
transformers: the product of two generators performs them in list order. -/
def generator (κ : Kind.{u, v} α) (atom : α) : (Function.End κ.State)ᵐᵒᵖ :=
  MulOpposite.op fun state => κ.add state atom

/-- **A batch is the list fold of the discipline.** -/
theorem insertBatch_eq_foldList (κ : Kind.{u, v} α) (state : κ.State) (batch : List α) :
    insertBatch κ state batch =
      (MulOpposite.unop (Mettapedia.Algebra.Collections.foldList (generator κ) batch)) state := by
  induction batch generalizing state with
  | nil => rfl
  | cons atom rest ih =>
      rw [insertBatch_cons, ih]
      rfl

/-- Order independence is commutation of the generators. -/
theorem orderIndependent_iff_commute (κ : Kind.{u, v} α) :
    OrderIndependent κ ↔ ∀ first second, Commute (generator κ first) (generator κ second) := by
  constructor
  · intro commute first second
    apply MulOpposite.unop_injective
    funext state
    exact commute state first second
  · intro commute state first second
    exact congrFun (congrArg MulOpposite.unop (commute first second)) state

/-- **Order independence is exactly commutation.** -/
theorem factorsThroughBag_iff (κ : Kind.{u, v} α) :
    (∀ state, FactorsThroughBag (insertBatch κ state)) ↔ OrderIndependent κ := by
  constructor
  · intro factors state first second
    exact factors state [first, second] [second, first] (List.Perm.swap _ _ _)
  · intro commute state first second permuted
    have : RightCommutative κ.add := ⟨commute⟩
    exact permuted.foldl_eq state

section Support

variable [DecidableEq α]

/-- With commuting, idempotent insertion, a repeated atom is absorbed. -/
theorem insertBatch_cons_of_mem {κ : Kind.{u, v} α} (commute : OrderIndependent κ)
    (idempotent : Idempotent κ) {atom : α} {batch : List α} (member : atom ∈ batch)
    (state : κ.State) : insertBatch κ state (atom :: batch) = insertBatch κ state batch := by
  have : RightCommutative κ.add := ⟨commute⟩
  have permuted : batch.Perm (atom :: batch.erase atom) := List.perm_cons_erase member
  calc insertBatch κ state (atom :: batch)
      = insertBatch κ (κ.add state atom) batch := rfl
    _ = insertBatch κ (κ.add state atom) (atom :: batch.erase atom) :=
        permuted.foldl_eq (κ.add state atom)
    _ = insertBatch κ (κ.add (κ.add state atom) atom) (batch.erase atom) := rfl
    _ = insertBatch κ (κ.add state atom) (batch.erase atom) := by rw [idempotent]
    _ = insertBatch κ state (atom :: batch.erase atom) := rfl
    _ = insertBatch κ state batch := (permuted.foldl_eq state).symm

/-- **Deduplication changes nothing** for a commuting, idempotent discipline. -/
theorem insertBatch_dedup {κ : Kind.{u, v} α} (commute : OrderIndependent κ)
    (idempotent : Idempotent κ) (batch : List α) (state : κ.State) :
    insertBatch κ state batch.dedup = insertBatch κ state batch := by
  induction batch generalizing state with
  | nil => rfl
  | cons atom rest ih =>
      by_cases member : atom ∈ rest
      · rw [List.dedup_cons_of_mem member, ih,
          insertBatch_cons_of_mem commute idempotent member]
      · rw [List.dedup_cons_of_notMem member, insertBatch_cons, ih, insertBatch_cons]

/-- **Duplicate insensitivity is commutation and idempotence.** -/
theorem factorsThroughSupport_iff (κ : Kind.{u, v} α) :
    (∀ state, FactorsThroughSupport (insertBatch κ state)) ↔
      OrderIndependent κ ∧ Idempotent κ := by
  constructor
  · intro factors
    refine ⟨(factorsThroughBag_iff κ).mp fun state => (factors state).perm_invariant, ?_⟩
    intro state atom
    exact (factors state [atom, atom] [atom] (by simp)).trans rfl
  · rintro ⟨commute, idempotent⟩ state first second same
    have permuted : first.dedup.Perm second.dedup := List.toFinset_eq_iff_perm_dedup.mp same
    rw [← insertBatch_dedup commute idempotent first, ← insertBatch_dedup commute idempotent second]
    exact (factorsThroughBag_iff κ).mpr commute state _ _ permuted

end Support

/-! ## The kinds -/

section Kinds

variable [DecidableEq α]

theorem atom_orderIndependent : OrderIndependent (atomKind (α := α)) :=
  fun state first second => Multiset.cons_swap second first state

theorem set_orderIndependent : OrderIndependent (setKind (α := α)) :=
  fun state first second => Finset.insert_comm second first state

theorem set_idempotent : Idempotent (setKind (α := α)) :=
  fun state atom => Finset.insert_idem atom state

theorem orderedSet_idempotent : Idempotent (orderedSetKind (α := α)) := by
  intro state atom
  apply Subtype.ext
  change orderedInsert (orderedInsert state.1 atom) atom = orderedInsert state.1 atom
  unfold orderedInsert
  split_ifs with present <;> simp_all

/-- **A set is a duplicate-insensitive sink.** -/
theorem set_factorsThroughSupport (state : Finset α) :
    FactorsThroughSupport (insertBatch (setKind (α := α)) state) :=
  ((factorsThroughSupport_iff setKind).mpr ⟨set_orderIndependent, set_idempotent⟩) state

/-- **A bag is an order-independent sink.** -/
theorem atom_factorsThroughBag (state : Multiset α) :
    FactorsThroughBag (insertBatch (atomKind (α := α)) state) :=
  ((factorsThroughBag_iff atomKind).mpr atom_orderIndependent) state

/-- A batch inserted into a set is the union with its atoms. -/
theorem insertBatch_set (state : Finset α) (batch : List α) :
    insertBatch (setKind (α := α)) state batch = batch.toFinset ∪ state := by
  show batch.foldl (fun stored atom => insert atom stored) state = batch.toFinset ∪ state
  induction batch generalizing state with
  | nil => simp
  | cons atom rest ih =>
      rw [List.foldl_cons, ih]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto

/-- A batch inserted into a bag adds its bag. -/
theorem insertBatch_atom (state : Multiset α) (batch : List α) :
    insertBatch (atomKind (α := α)) state batch = (batch : Multiset α) + state := by
  show batch.foldl (fun stored atom => atom ::ₘ stored) state = (batch : Multiset α) + state
  induction batch generalizing state with
  | nil => simp
  | cons atom rest ih =>
      rw [List.foldl_cons, ih, Multiset.add_cons, ← Multiset.cons_coe, Multiset.cons_add]

end Kinds

/-! ## Removal batches -/

section Removal

/-- Remove a batch of instances, in the order given. -/
def removeBatch (κ : Kind.{u, v} α) (state : κ.State) (batch : List α) : κ.State :=
  batch.foldl κ.remove state

/-- Two removals commute. -/
def RemovalOrderIndependent (κ : Kind.{u, v} α) : Prop :=
  ∀ state first second,
    κ.remove (κ.remove state first) second = κ.remove (κ.remove state second) first

/-- Removing an atom again changes nothing. -/
def RemovalIdempotent (κ : Kind.{u, v} α) : Prop :=
  ∀ state atom, κ.remove (κ.remove state atom) atom = κ.remove state atom

/-- Removal batches of a kind are insertion batches of the kind whose insertion is
that removal; the theorems on batches apply to them. -/
def removalKind (κ : Kind.{u, v} α) : Kind.{u, v} α where
  State := κ.State
  empty := κ.empty
  contents := κ.contents
  add := κ.remove
  remove := κ.add

theorem removeBatch_eq (κ : Kind.{u, v} α) (state : κ.State) (batch : List α) :
    removeBatch κ state batch = insertBatch (removalKind κ) state batch :=
  rfl

variable [DecidableEq α]

theorem setRemove_orderIndependent : RemovalOrderIndependent (setKind (α := α)) :=
  fun _ _ _ => Finset.erase_right_comm

theorem setRemove_idempotent : RemovalIdempotent (setKind (α := α)) :=
  fun _ _ => Finset.erase_idem

theorem atomRemove_orderIndependent : RemovalOrderIndependent (atomKind (α := α)) :=
  fun state first second => Multiset.erase_comm state first second

/-- **MM2's `-` sink is duplicate insensitive.** -/
theorem setRemove_factorsThroughSupport (state : Finset α) :
    FactorsThroughSupport (removeBatch (setKind (α := α)) state) :=
  ((factorsThroughSupport_iff (removalKind setKind)).mpr
    ⟨setRemove_orderIndependent, setRemove_idempotent⟩) state

end Removal

/-! ## One MM2 firing -/

section Firing

variable {Match : Type v} [DecidableEq α]

/-- One firing in the kernel's order: insert every `+` instance, then remove every
`-` instance. -/
def kernelStep (plus minus : Match → α) (state : Finset α) (rows : List Match) : Finset α :=
  (rows.map minus).foldl (fun stored atom => stored.erase atom)
    ((rows.map plus).foldl (fun stored atom => insert atom stored) state)

/-- The firing is a removal batch of the set kind after an insertion batch. -/
theorem kernelStep_eq_batches (plus minus : Match → α) (state : Finset α) (rows : List Match) :
    kernelStep plus minus state rows =
      removeBatch setKind (insertBatch setKind state (rows.map plus)) (rows.map minus) :=
  rfl

/-- The firing as sets: `(state ∪ added) \ removed`. -/
theorem kernelStep_eq (plus minus : Match → α) (state : Finset α) (rows : List Match) :
    kernelStep plus minus state rows =
      ((rows.map plus).toFinset ∪ state) \ (rows.map minus).toFinset := by
  have adds : ∀ (start : Finset α) (batch : List α),
      batch.foldl (fun stored atom => insert atom stored) start = batch.toFinset ∪ start := by
    intro start batch
    induction batch generalizing start with
    | nil => simp
    | cons atom rest ih =>
        rw [List.foldl_cons, ih]
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
  have removes : ∀ (start : Finset α) (batch : List α),
      batch.foldl (fun stored atom => stored.erase atom) start = start \ batch.toFinset := by
    intro start batch
    induction batch generalizing start with
    | nil => simp
    | cons atom rest ih =>
        rw [List.foldl_cons, ih]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
        tauto
  unfold kernelStep
  rw [adds, removes]

/-- **One firing depends only on the set of matches.** -/
theorem kernelStep_factorsThroughSupport [DecidableEq Match] (plus minus : Match → α)
    (state : Finset α) :
    FactorsThroughSupport (kernelStep plus minus state) := by
  intro first second same
  have mapped (f : Match → α) : (first.map f).toFinset = (second.map f).toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_map]
    constructor <;> rintro ⟨row, member, rfl⟩ <;> refine ⟨row, ?_, rfl⟩
    · rw [← List.mem_toFinset, ← same, List.mem_toFinset]
      exact member
    · rw [← List.mem_toFinset, same, List.mem_toFinset]
      exact member
  rw [kernelStep_eq, kernelStep_eq, mapped plus, mapped minus]

end Firing

/-! ## Dicts: the policies as sinks -/

section Dicts

variable {Key Val : Type*} [DecidableEq Key] [DecidableEq Val]

omit [DecidableEq Key] [DecidableEq Val] in
/-- Two functional dicts with the same lookup are equal. -/
theorem functional_ext {first second : Finset (Key × Val)} (firstFunctional : FunctionalSet first)
    (secondFunctional : FunctionalSet second) (same : ∀ key, lookup first key = lookup second key) :
    first = second := by
  ext ⟨key, value⟩
  rw [← lookup_eq_some_iff firstFunctional, ← lookup_eq_some_iff secondFunctional, same]

/-- The stored set of a dict after `add-atom`, when the policy stores. -/
theorem dictKind_add_of_put {policy : UpdatePolicy Val}
    (state : (dictKind (Key := Key) (Val := Val) policy).State) (key : Key) (value : Val)
    (updated : Finset (Key × Val)) (stores : put policy state.1 key value = some updated) :
    ((dictKind policy).add state (key, value)).1 = updated := by
  change (match stores' : put policy state.1 key value with
    | some updated' => (⟨updated', functional_put state.2 policy key value updated' stores'⟩ :
        {stored : Finset (Key × Val) // FunctionalSet stored})
    | none => state).1 = updated
  split
  · rename_i updated' found
    rw [stores] at found
    cases found
    rfl
  · rename_i found
    rw [stores] at found
    cases found

/-- A refused pair leaves the dict as it was. -/
theorem dictKind_add_of_refused {policy : UpdatePolicy Val}
    (state : (dictKind (Key := Key) (Val := Val) policy).State) (key : Key) (value : Val)
    (refused : put policy state.1 key value = none) :
    (dictKind policy).add state (key, value) = state := by
  change (match stores' : put policy state.1 key value with
    | some updated' => (⟨updated', functional_put state.2 policy key value updated' stores'⟩ :
        {stored : Finset (Key × Val) // FunctionalSet stored})
    | none => state) = state
  split
  · rename_i updated' found
    rw [refused] at found
    cases found
  · rfl

/-- The lookup after merging. -/
theorem lookup_merge_add (combine : Val → Val → Val)
    (state : (dictKind (Key := Key) (Val := Val) (.merge combine)).State) (key other : Key)
    (value : Val) :
    lookup ((dictKind (.merge combine)).add state (key, value)).1 other =
      if other = key then
        some (match lookup state.1 key with
          | some old => combine old value
          | none => value)
      else lookup state.1 other := by
  have stores : put (.merge combine) state.1 key value = some (replaceValue state.1 key
      (match lookup state.1 key with
        | some old => combine old value
        | none => value)) := rfl
  rw [dictKind_add_of_put state key value _ stores]
  split_ifs with same
  · subst same
    exact lookup_replaceValue state.2 other _
  · exact lookup_replaceValue_other state.2 key other same _

/-- **Merging by a commutative, associative operation is order independent.** -/
theorem merge_orderIndependent (combine : Val → Val → Val)
    (commutative : ∀ a b, combine a b = combine b a)
    (associative : ∀ a b c, combine (combine a b) c = combine a (combine b c)) :
    OrderIndependent (dictKind (Key := Key) (Val := Val) (.merge combine)) := by
  rintro state ⟨key₁, value₁⟩ ⟨key₂, value₂⟩
  apply Subtype.ext
  apply functional_ext ((dictKind (.merge combine)).add _ _).2 ((dictKind (.merge combine)).add _ _).2
  intro other
  simp only [lookup_merge_add]
  by_cases first : other = key₂ <;> by_cases second : other = key₁
  · subst first
    subst second
    simp only [if_true]
    cases lookup state.1 other with
    | none => simp [commutative]
    | some old => simp [associative, commutative value₁]
  · subst first
    simp [second]
  · subst second
    simp [first]
  · simp [first, second]

/-- **Merging is duplicate insensitive exactly for an idempotent operation**
(given associativity). -/
theorem merge_idempotent_iff [Inhabited Key] (combine : Val → Val → Val)
    (associative : ∀ a b c, combine (combine a b) c = combine a (combine b c)) :
    Idempotent (dictKind (Key := Key) (Val := Val) (.merge combine)) ↔
      ∀ a, combine a a = a := by
  constructor
  · intro idempotent a
    let empty : (dictKind (Key := Key) (Val := Val) (.merge combine)).State :=
      (dictKind (.merge combine)).empty
    have emptyLookup : lookup empty.1 default = none :=
      (lookup_eq_none_iff _ _).mpr fun _ member => absurd member (Finset.notMem_empty _)
    have same := congrArg (fun state : (dictKind (Key := Key) (Val := Val) (.merge combine)).State =>
      lookup state.1 default) (idempotent empty (default, a))
    simp only [lookup_merge_add, if_true, emptyLookup] at same
    exact Option.some.inj same
  · intro idem state ⟨key, value⟩
    apply Subtype.ext
    apply functional_ext ((dictKind (.merge combine)).add _ _).2 ((dictKind (.merge combine)).add _ _).2
    intro other
    simp only [lookup_merge_add]
    split_ifs with same
    · cases lookup state.1 key with
      | none => simp [idem]
      | some old => simp [associative, idem]
    · rfl

/-- The lookup after storing by replacement. -/
theorem lookup_replace_add (state : (dictKind (Key := Key) (Val := Val) .replace).State)
    (key other : Key) (value : Val) :
    lookup ((dictKind .replace).add state (key, value)).1 other =
      if other = key then some value else lookup state.1 other := by
  rw [dictKind_add_of_put state key value _ rfl]
  split_ifs with same
  · subst same
    exact lookup_replaceValue state.2 other value
  · exact lookup_replaceValue_other state.2 key other same value

/-- The lookup after storing unless a value is there. -/
theorem lookup_keepFirst_add (state : (dictKind (Key := Key) (Val := Val) .keepFirst).State)
    (key other : Key) (value : Val) :
    lookup ((dictKind .keepFirst).add state (key, value)).1 other =
      if other = key then (lookup state.1 key).or (some value) else lookup state.1 other := by
  cases found : lookup state.1 key with
  | some old =>
      have stores : put .keepFirst state.1 key value = some state.1 := by simp [put, found]
      rw [dictKind_add_of_put state key value _ stores]
      split_ifs with same
      · subst same
        simp [found]
      · rfl
  | none =>
      have stores : put .keepFirst state.1 key value = some (replaceValue state.1 key value) := by
        simp [put, found]
      rw [dictKind_add_of_put state key value _ stores]
      split_ifs with same
      · subst same
        simpa using lookup_replaceValue state.2 other value
      · exact lookup_replaceValue_other state.2 key other same value

/-- The lookup after storing by the reject policy: a stored key refuses. -/
theorem lookup_reject_add (state : (dictKind (Key := Key) (Val := Val) .reject).State)
    (key other : Key) (value : Val) :
    lookup ((dictKind .reject).add state (key, value)).1 other =
      if other = key then (lookup state.1 key).or (some value) else lookup state.1 other := by
  cases found : lookup state.1 key with
  | some old =>
      rw [dictKind_add_of_refused state key value
        ((put_reject_eq_none_iff _ _ _).mpr (by simp [found]))]
      split_ifs with same
      · subst same
        simp [found]
      · rfl
  | none =>
      have stores : put .reject state.1 key value = some (replaceValue state.1 key value) := by
        simp [put, found]
      rw [dictKind_add_of_put state key value _ stores]
      split_ifs with same
      · subst same
        simpa using lookup_replaceValue state.2 other value
      · exact lookup_replaceValue_other state.2 key other same value

/-- Replacement is duplicate insensitive. -/
theorem replace_idempotent : Idempotent (dictKind (Key := Key) (Val := Val) .replace) := by
  intro state ⟨key, value⟩
  apply Subtype.ext
  apply functional_ext ((dictKind .replace).add _ _).2 ((dictKind .replace).add _ _).2
  intro other
  simp only [lookup_replace_add]
  split_ifs <;> rfl

/-- Keeping the first value is duplicate insensitive. -/
theorem keepFirst_idempotent : Idempotent (dictKind (Key := Key) (Val := Val) .keepFirst) := by
  intro state ⟨key, value⟩
  apply Subtype.ext
  apply functional_ext ((dictKind .keepFirst).add _ _).2 ((dictKind .keepFirst).add _ _).2
  intro other
  simp only [lookup_keepFirst_add, if_true]
  split_ifs
  · cases lookup state.1 key <;> rfl
  · rfl

/-- The reject policy that drops a second value is duplicate insensitive. -/
theorem reject_idempotent : Idempotent (dictKind (Key := Key) (Val := Val) .reject) := by
  intro state ⟨key, value⟩
  apply Subtype.ext
  apply functional_ext ((dictKind .reject).add _ _).2 ((dictKind .reject).add _ _).2
  intro other
  simp only [lookup_reject_add, if_true]
  split_ifs
  · cases lookup state.1 key <;> rfl
  · rfl

/-! ### Refusing the whole batch

The reject policy is order independent when a second value fails the batch
instead of being dropped: the state is a dict or a conflict, and a conflict
absorbs everything after it. -/

/-- Store a pair unless its key holds another value; a conflict is final. -/
def conflictPut (state : Option (Key → Option Val)) (pair : Key × Val) :
    Option (Key → Option Val) :=
  match state with
  | none => none
  | some graph =>
      match graph pair.1 with
      | none => some (Function.update graph pair.1 (some pair.2))
      | some old => if old = pair.2 then some graph else none

/-- The dict sink that refuses a second value by failing the batch. -/
def conflictKind : Kind (Key × Val) where
  State := Option (Key → Option Val)
  empty := some fun _ => none
  contents _ := 0
  add := conflictPut
  remove state _ := state

theorem conflictPut_idempotent : Idempotent (conflictKind (Key := Key) (Val := Val)) := by
  rintro (_ | graph) ⟨key, value⟩
  · rfl
  · change conflictPut (conflictPut (some graph) (key, value)) (key, value) =
      conflictPut (some graph) (key, value)
    cases found : graph key with
    | none => simp [conflictPut, found]
    | some old =>
        by_cases same : old = value
        · simp [conflictPut, found, same]
        · simp [conflictPut, found, same]

theorem conflictPut_orderIndependent :
    OrderIndependent (conflictKind (Key := Key) (Val := Val)) := by
  rintro (_ | graph) ⟨key₁, value₁⟩ ⟨key₂, value₂⟩
  · rfl
  · change conflictPut (conflictPut (some graph) (key₁, value₁)) (key₂, value₂) =
      conflictPut (conflictPut (some graph) (key₂, value₂)) (key₁, value₁)
    by_cases sameKey : key₁ = key₂
    · subst sameKey
      cases found : graph key₁ with
      | none =>
          by_cases sameValue : value₁ = value₂
          · subst sameValue; rfl
          · simp [conflictPut, found, sameValue, Ne.symm sameValue]
      | some old =>
          by_cases first : old = value₁
          · by_cases second : old = value₂
            · subst first
              subst second
              rfl
            · subst first
              simp [conflictPut, found, second]
          · by_cases second : old = value₂
            · subst second
              simp [conflictPut, found, first]
            · simp [conflictPut, found, first, second]
    · cases found₁ : graph key₁ with
      | none =>
          cases found₂ : graph key₂ with
          | none =>
              simp only [conflictPut, found₁, found₂, Function.update_of_ne sameKey,
                Function.update_of_ne (Ne.symm sameKey)]
              rw [Function.update_comm sameKey]
          | some old₂ =>
              by_cases second : old₂ = value₂ <;>
                simp [conflictPut, found₁, found₂, second, Function.update_of_ne (Ne.symm sameKey)]
      | some old₁ =>
          cases found₂ : graph key₂ with
          | none =>
              by_cases first : old₁ = value₁ <;>
                simp [conflictPut, found₁, found₂, first, Function.update_of_ne sameKey]
          | some old₂ =>
              by_cases first : old₁ = value₁ <;> by_cases second : old₂ = value₂ <;>
                simp [conflictPut, found₁, found₂, first, second]

end Dicts

/-! ## Controls -/

namespace Controls

/-- A bag counts a repeat. -/
theorem atom_not_idempotent : ¬ Idempotent (atomKind (α := ℕ)) := by
  intro idempotent
  have := congrArg Multiset.card (idempotent (0 : Multiset ℕ) 0)
  simp [atomKind] at this

/-- Removing one occurrence twice removes two. -/
theorem atomRemove_not_idempotent : ¬ RemovalIdempotent (atomKind (α := ℕ)) := by
  intro idempotent
  have := idempotent ({0, 0} : Multiset ℕ) 0
  simp [atomKind] at this

/-- **A queue fed by an unordered join leaks the enumeration order.** -/
theorem history_order_dependent (removal : End) : ¬ OrderIndependent (historyKind (α := ℕ) removal) := by
  intro commute
  have := commute ([] : List ℕ) 0 1
  simp [historyKind] at this

/-- **An insertion-ordered set (`unique-atom`) leaks the enumeration order.** -/
theorem orderedSet_order_dependent : ¬ OrderIndependent (orderedSetKind (α := ℕ)) := by
  intro commute
  have := congrArg Subtype.val (commute ⟨[], List.nodup_nil⟩ 0 1)
  simp [orderedSetKind, orderedInsert] at this

/-- A dict holding nothing. -/
noncomputable def emptyDict (policy : UpdatePolicy ℕ) : (dictKind (Key := Unit) (Val := ℕ) policy).State :=
  (dictKind policy).empty

theorem lookup_empty (key : Unit) : lookup (∅ : Finset (Unit × ℕ)) key = none :=
  (lookup_eq_none_iff _ _).mpr fun _ member => absurd member (Finset.notMem_empty _)

/-- The value found after storing two values under one key by a policy, in the
given order. -/
noncomputable def twoPuts (policy : UpdatePolicy ℕ) (first second : ℕ) : Option ℕ :=
  lookup ((dictKind policy).add ((dictKind policy).add (emptyDict policy) ((), first))
    ((), second)).1 ()

theorem lookup_add_replace (state : (dictKind (Key := Unit) (Val := ℕ) .replace).State)
    (value : ℕ) : lookup ((dictKind .replace).add state ((), value)).1 () = some value := by
  rw [dictKind_add_of_put state () value _ rfl]
  exact lookup_replaceValue state.2 () value

/-- **A last-writer-wins dict leaks the enumeration order.** -/
theorem replace_order_dependent : ¬ OrderIndependent (dictKind (Key := Unit) (Val := ℕ) .replace) := by
  intro commute
  have same := congrArg (fun state : (dictKind (Key := Unit) (Val := ℕ) .replace).State =>
    lookup state.1 ()) (commute (emptyDict .replace) ((), 1) ((), 2))
  simp only [lookup_add_replace] at same
  cases same

theorem lookup_add_keepFirst_empty (value : ℕ) :
    lookup ((dictKind (Key := Unit) (Val := ℕ) .keepFirst).add (emptyDict .keepFirst)
      ((), value)).1 () = some value := by
  have stores : put (Key := Unit) .keepFirst (∅ : Finset (Unit × ℕ)) () value =
      some (replaceValue ∅ () value) := by
    simp [put, lookup_empty]
  rw [dictKind_add_of_put (emptyDict .keepFirst) () value _ stores]
  exact lookup_replaceValue (emptyDict .keepFirst).2 () value

theorem lookup_add_keepFirst_full (state : (dictKind (Key := Unit) (Val := ℕ) .keepFirst).State)
    (old value : ℕ) (found : lookup state.1 () = some old) :
    lookup ((dictKind .keepFirst).add state ((), value)).1 () = some old := by
  have stores : put .keepFirst state.1 () value = some state.1 := by
    simp [put, found]
  rw [dictKind_add_of_put state () value _ stores, found]

/-- **A first-writer-wins dict leaks the enumeration order.** -/
theorem keepFirst_order_dependent :
    ¬ OrderIndependent (dictKind (Key := Unit) (Val := ℕ) .keepFirst) := by
  intro commute
  have same := congrArg (fun state : (dictKind (Key := Unit) (Val := ℕ) .keepFirst).State =>
    lookup state.1 ()) (commute (emptyDict .keepFirst) ((), 1) ((), 2))
  rw [lookup_add_keepFirst_full _ 1 2 (lookup_add_keepFirst_empty 1),
    lookup_add_keepFirst_full _ 2 1 (lookup_add_keepFirst_empty 2)] at same
  cases same

theorem lookup_add_reject_empty (value : ℕ) :
    lookup ((dictKind (Key := Unit) (Val := ℕ) .reject).add (emptyDict .reject)
      ((), value)).1 () = some value := by
  have stores : put (Key := Unit) .reject (∅ : Finset (Unit × ℕ)) () value =
      some (replaceValue ∅ () value) := by
    simp [put, lookup_empty]
  rw [dictKind_add_of_put (emptyDict .reject) () value _ stores]
  exact lookup_replaceValue (emptyDict .reject).2 () value

theorem lookup_add_reject_full (state : (dictKind (Key := Unit) (Val := ℕ) .reject).State)
    (old value : ℕ) (found : lookup state.1 () = some old) :
    lookup ((dictKind .reject).add state ((), value)).1 () = some old := by
  rw [dictKind_add_of_refused state () value ((put_reject_eq_none_iff _ _ _).mpr (by simp [found])),
    found]

/-- **A reject policy that drops the second value leaks the enumeration order**:
whichever value arrives first stays. -/
theorem reject_order_dependent :
    ¬ OrderIndependent (dictKind (Key := Unit) (Val := ℕ) .reject) := by
  intro commute
  have same := congrArg (fun state : (dictKind (Key := Unit) (Val := ℕ) .reject).State =>
    lookup state.1 ()) (commute (emptyDict .reject) ((), 1) ((), 2))
  rw [lookup_add_reject_full _ 1 2 (lookup_add_reject_empty 1),
    lookup_add_reject_full _ 2 1 (lookup_add_reject_empty 2)] at same
  cases same

/-- Failing the batch instead: both orders end in a conflict. -/
theorem conflict_both_orders :
    insertBatch (conflictKind (Key := Unit) (Val := ℕ)) conflictKind.empty [((), 1), ((), 2)] = none ∧
      insertBatch (conflictKind (Key := Unit) (Val := ℕ)) conflictKind.empty [((), 2), ((), 1)] =
        none := by
  constructor <;> rfl

/-- **Merging by addition counts a repeat**: order independent, as a bag, and not
duplicate insensitive. -/
theorem mergeAdd_not_idempotent :
    ¬ Idempotent (dictKind (Key := Unit) (Val := ℕ) (.merge (· + ·))) := by
  intro idempotent
  have same := congrArg (fun state : (dictKind (Key := Unit) (Val := ℕ) (.merge (· + ·))).State =>
    lookup state.1 ()) (idempotent (emptyDict (.merge (· + ·))) ((), 1))
  simp only [lookup_merge_add, if_true] at same
  have empty : lookup (emptyDict (.merge (· + ·))).1 () = none := lookup_empty ()
  rw [empty] at same
  simp at same

theorem mergeAdd_orderIndependent :
    OrderIndependent (dictKind (Key := Unit) (Val := ℕ) (.merge (· + ·))) :=
  merge_orderIndependent _ Nat.add_comm Nat.add_assoc

end Controls

end Mettapedia.Languages.MeTTa.SpaceSinks
