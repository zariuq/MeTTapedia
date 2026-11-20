import Mathlib

/-!
# Predicate queries, aggregate queries, and the promotion of speculative results

A store is a bag of rows, `Multiset R`.

## Queries are folds

A **query** of a bag is the fold of a per-row map into a commutative monoid,
`query f rows = (rows.map f).sum`. It is the unique monoid map out of the free commutative
monoid `Multiset R` that extends `f` (`collect_initial`). The query `collectQuery` folds the
singleton map and returns the bag itself (`collectQuery_eq`), so every query factors through it
(`query_eq_queryHom_collect`, `queryHom_restrict`).

## Predicate queries

A **predicate query** is a fold into an idempotent target: a join-semilattice with bottom
(`supQuery`, built on `Multiset.sup`), a meet-semilattice with top (`infQuery`, on
`Multiset.inf`), or a commutative monoid with `m + m = m`. Such a fold sees only the set of rows
(`query_eq_sum_toFinset_of_idempotent`, `supQuery_eq_finset_sup`).

* `existsQuery p` is the supremum in the lattice `Bool`, `forallQuery p` the infimum, and
  `noneQuery p` the negation of `existsQuery p`. Each equals its logical specification
  (`existsQuery_eq_true_iff`, `forallQuery_eq_true_iff`, `noneQuery_eq_true_iff`).
* `bestQuery w` is the supremum in `WithBot β` of the weights: `⊥` on the empty bag
  (`bestQuery_eq_bot_iff`), and the largest weight otherwise (`bestQuery_eq_coe_iff`). The rows
  that attain it are the witnesses of the ∃∀ formula (`IsBest`, `mem_bestRows`,
  `exists_isBest`). With a linear order on rows to break ties, one witness is itself a fold into
  a semilattice (`bestWitness`, `bestWitness_spec`).
* Each is invariant under `dedup` (`existsQuery_dedup`, `forallQuery_dedup`, `noneQuery_dedup`,
  `bestQuery_dedup`, `mem_bestRows_dedup`, `bestWitness_dedup`).

## Aggregate queries

`countQuery`, `sumQuery`, `parityQuery` and `collectQuery` are folds into commutative monoids
that are not idempotent; they see multiplicities.

## Separation

A function of bags is `DedupInvariant` when removing duplicate rows never changes it; equivalently
it depends only on which rows occur (`dedupInvariant_iff`). Every fold into an idempotent target
is dedup-invariant, and no dedup-invariant function, followed by any readout, computes `count`,
`parity` or a nonzero `sum` (`not_computes_of_dedupInvariant`). Hence no predicate query computes
`count` or `parity` (`idempotent_query_not_count`, `supQuery_not_count`, `infQuery_not_count`,
and the `parity` forms), while every query factors through `collect`.

The separation is exactly about multiplicity. The number of distinct rows is a readout of a
predicate query (`countAnswers_eq_card_supQuery`). That parity of the number of distinct rows is
not expressible by first-order ∃/∀ formulas over the set is a separate theorem of finite model
theory, not proved here.

## Basis

* `forallQuery` with negation generates `existsQuery` and `noneQuery`
  (`existsQuery_eq_not_forallQuery`, `noneQuery_eq_forallQuery_not`).
* `bestQuery` is the ∃∀ formula built from `existsQuery` and `forallQuery`
  (`bestQuery_eq_coe_iff_existsQuery`, `isBest_iff_forallQuery`).
* "At least `k` distinct rows satisfy `p`", for a fixed `k`, is the statement that there are `k`
  pairwise distinct witnesses satisfying `p` (`atLeast_iff_distinct_witnesses`); it depends only
  on the set of rows (`atLeast_dedup`). Returning the count as data is the aggregate
  `countWhere`, which no predicate query computes (`countWhere_not_dedupInvariant`). Over a store of
  occurrences with identities, "at least `k` occurrences in a region" has the same distinct-witness
  form (`atLeast_occurrences_iff`).

## Occurrences and answers

`countQuery` counts rows with multiplicity; `countAnswers bind` counts distinct bindings. They
agree exactly when the bindings are pairwise distinct (`countAnswers_eq_countQuery_iff`), and
differ on two rows with one binding (`occurrences_ne_answers`).

The promotion of speculative results that rests on these queries is in
`Mettapedia.GSLT.Core.SpeculativePromotion`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.RegionQueries

universe u v w

theorem ne_zero_of_mem {α : Type*} {s : Multiset α} {a : α} (h : a ∈ s) :
    s ≠ 0 := by
  rintro rfl
  simp at h

/-! ## Queries are folds -/

section Fold

variable {R : Type u} {M : Type v} [AddCommMonoid M]

/-- The query determined by `f`: fold the per-row values of a bag into `M`. -/
def query (f : R → M) (rows : Multiset R) : M := (rows.map f).sum

@[simp] theorem query_zero (f : R → M) : query f 0 = 0 := by simp [query]

@[simp] theorem query_cons (f : R → M) (r : R) (rows : Multiset R) :
    query f (r ::ₘ rows) = f r + query f rows := by simp [query]

@[simp] theorem query_singleton (f : R → M) (r : R) : query f {r} = f r := by simp [query]

theorem query_add (f : R → M) (s t : Multiset R) : query f (s + t) = query f s + query f t := by
  simp [query]

/-- The query of `f` as a monoid map out of the free commutative monoid on rows. -/
def queryHom (f : R → M) : Multiset R →+ M :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom f)

@[simp] theorem queryHom_apply (f : R → M) (rows : Multiset R) :
    queryHom f rows = query f rows := rfl

/-- `collect`: the query of the singleton map, a fold into the free commutative monoid. -/
def collectQuery (rows : Multiset R) : Multiset R := query (fun r => {r}) rows

/-- `collect` returns the bag itself. -/
@[simp] theorem collectQuery_eq (rows : Multiset R) : collectQuery rows = rows :=
  Multiset.sum_map_singleton rows

/-- **`collect` is initial.** For every per-row map there is exactly one monoid map out of the
bags of rows that extends it. -/
theorem collect_initial (f : R → M) : ∃! h : Multiset R →+ M, ∀ r, h {r} = f r :=
  ⟨queryHom f, fun r => by simp, fun h hf => Multiset.addHom_ext fun r => by simp [hf]⟩

/-- **Every query factors through `collect`.** -/
theorem query_eq_queryHom_collect (f : R → M) (rows : Multiset R) :
    query f rows = queryHom f (collectQuery rows) := by simp

/-- Every monoid map out of the bags of rows is the query of its values on single rows. -/
theorem queryHom_restrict (F : Multiset R →+ M) : queryHom (fun r => F {r}) = F :=
  Multiset.addHom_ext fun r => by simp

end Fold

/-! ## Folds into idempotent targets -/

section Idempotent

variable {R : Type u} [DecidableEq R] {M : Type v} [AddCommMonoid M]

/-- With an idempotent target, a query sees only which rows occur. -/
theorem query_eq_sum_toFinset_of_idempotent (idem : ∀ m : M, m + m = m) (f : R → M)
    (rows : Multiset R) : query f rows = ∑ r ∈ rows.toFinset, f r := by
  induction rows using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [query_cons, ih, Multiset.toFinset_cons]
      by_cases mem : a ∈ s.toFinset
      · rw [Finset.insert_eq_of_mem mem, ← Finset.add_sum_erase _ _ mem, ← add_assoc, idem]
      · rw [Finset.sum_insert mem]

theorem query_dedup_of_idempotent (idem : ∀ m : M, m + m = m) (f : R → M)
    (rows : Multiset R) : query f rows.dedup = query f rows := by
  rw [query_eq_sum_toFinset_of_idempotent idem, query_eq_sum_toFinset_of_idempotent idem,
    Multiset.toFinset_dedup]

end Idempotent

section Semilattice

variable {R : Type u} {M : Type v}

/-- The fold of `f` into a join-semilattice with bottom. -/
def supQuery [SemilatticeSup M] [OrderBot M] (f : R → M) (rows : Multiset R) : M :=
  (rows.map f).sup

/-- The fold of `f` into a meet-semilattice with top. -/
def infQuery [SemilatticeInf M] [OrderTop M] (f : R → M) (rows : Multiset R) : M :=
  (rows.map f).inf

section Sup

variable [SemilatticeSup M] [OrderBot M] (f : R → M)

@[simp] theorem supQuery_zero : supQuery f 0 = ⊥ := by simp [supQuery]

@[simp] theorem supQuery_cons (r : R) (rows : Multiset R) :
    supQuery f (r ::ₘ rows) = f r ⊔ supQuery f rows := by simp [supQuery]

theorem supQuery_add (s t : Multiset R) : supQuery f (s + t) = supQuery f s ⊔ supQuery f t := by
  simp [supQuery]

theorem supQuery_le_iff {rows : Multiset R} {m : M} :
    supQuery f rows ≤ m ↔ ∀ r ∈ rows, f r ≤ m := by
  simp [supQuery, Multiset.sup_le]

theorem le_supQuery {rows : Multiset R} {r : R} (h : r ∈ rows) : f r ≤ supQuery f rows :=
  (supQuery_le_iff f).mp le_rfl r h

/-- A join-fold is monotone in the set of rows. -/
theorem supQuery_mono {s t : Multiset R} (h : s ⊆ t) : supQuery f s ≤ supQuery f t :=
  Multiset.sup_mono (Multiset.map_subset_map h)

/-- A join-fold depends only on which rows occur. -/
theorem supQuery_congr {s t : Multiset R} (h : ∀ r, r ∈ s ↔ r ∈ t) :
    supQuery f s = supQuery f t :=
  le_antisymm (supQuery_mono f fun r hr => (h r).mp hr)
    (supQuery_mono f fun r hr => (h r).mpr hr)

variable [DecidableEq R]

theorem supQuery_dedup (rows : Multiset R) : supQuery f rows.dedup = supQuery f rows :=
  supQuery_congr f fun _ => Multiset.mem_dedup

/-- A join-fold is the supremum over the set of rows. -/
theorem supQuery_eq_finset_sup (rows : Multiset R) : supQuery f rows = rows.toFinset.sup f := by
  rw [Finset.sup_def, Multiset.toFinset_val, ← supQuery, supQuery_dedup]

end Sup

section Inf

variable [SemilatticeInf M] [OrderTop M] (f : R → M)

@[simp] theorem infQuery_zero : infQuery f 0 = ⊤ := by simp [infQuery]

@[simp] theorem infQuery_cons (r : R) (rows : Multiset R) :
    infQuery f (r ::ₘ rows) = f r ⊓ infQuery f rows := by simp [infQuery]

theorem infQuery_add (s t : Multiset R) : infQuery f (s + t) = infQuery f s ⊓ infQuery f t := by
  simp [infQuery]

theorem le_infQuery_iff {rows : Multiset R} {m : M} :
    m ≤ infQuery f rows ↔ ∀ r ∈ rows, m ≤ f r := by
  simp [infQuery, Multiset.le_inf]

/-- A meet-fold is antitone in the set of rows. -/
theorem infQuery_anti {s t : Multiset R} (h : s ⊆ t) : infQuery f t ≤ infQuery f s :=
  Multiset.inf_mono (Multiset.map_subset_map h)

/-- A meet-fold depends only on which rows occur. -/
theorem infQuery_congr {s t : Multiset R} (h : ∀ r, r ∈ s ↔ r ∈ t) :
    infQuery f s = infQuery f t :=
  le_antisymm (infQuery_anti f fun r hr => (h r).mpr hr)
    (infQuery_anti f fun r hr => (h r).mp hr)

variable [DecidableEq R]

theorem infQuery_dedup (rows : Multiset R) : infQuery f rows.dedup = infQuery f rows :=
  infQuery_congr f fun _ => Multiset.mem_dedup

/-- A meet-fold is the infimum over the set of rows. -/
theorem infQuery_eq_finset_inf (rows : Multiset R) : infQuery f rows = rows.toFinset.inf f := by
  rw [Finset.inf_def, Multiset.toFinset_val, ← infQuery, infQuery_dedup]

end Inf

end Semilattice

/-! ## Predicate queries in `Bool` -/

section Predicate

variable {R : Type u} (p : R → Bool)

/-- `exists`: some row satisfies `p`. The join-fold into the lattice `Bool` (`⊔` is `or`, `⊥` is
`false`). The computable lattice instances of `Bool` are named, since the complete-lattice instance
is noncomputable. -/
def existsQuery (rows : Multiset R) : Bool :=
  @supQuery R Bool Bool.instDistribLattice.toSemilatticeSup Bool.instBoundedOrder.toOrderBot p rows

/-- `forall`: every row satisfies `p`. The meet-fold into the lattice `Bool` (`⊓` is `and`, `⊤` is
`true`). -/
def forallQuery (rows : Multiset R) : Bool :=
  @infQuery R Bool Bool.instDistribLattice.toSemilatticeInf Bool.instBoundedOrder.toOrderTop p rows

/-- `none`: no row satisfies `p`. It is the meet-fold of `!p` (`noneQuery_eq_forallQuery_not`). -/
def noneQuery (rows : Multiset R) : Bool := !existsQuery p rows

theorem existsQuery_eq_false_iff {rows : Multiset R} :
    existsQuery p rows = false ↔ ∀ r ∈ rows, p r = false := by
  have key : ∀ b : Bool, b ≤ false ↔ b = false := fun b => by cases b <;> decide
  rw [existsQuery, ← key, supQuery_le_iff]
  simp only [key]

/-- `exists` meets its specification. -/
theorem existsQuery_eq_true_iff {rows : Multiset R} :
    existsQuery p rows = true ↔ ∃ r ∈ rows, p r = true := by
  rw [← Bool.not_eq_false, existsQuery_eq_false_iff]
  simp

/-- `forall` meets its specification. -/
theorem forallQuery_eq_true_iff {rows : Multiset R} :
    forallQuery p rows = true ↔ ∀ r ∈ rows, p r = true := by
  have key : ∀ b : Bool, true ≤ b ↔ b = true := fun b => by cases b <;> decide
  rw [forallQuery, ← key, le_infQuery_iff]
  simp only [key]

/-- `none` meets its specification. -/
theorem noneQuery_eq_true_iff {rows : Multiset R} :
    noneQuery p rows = true ↔ ∀ r ∈ rows, p r = false := by
  rw [noneQuery, Bool.not_eq_true', existsQuery_eq_false_iff]

theorem noneQuery_eq_true_iff_not_exists {rows : Multiset R} :
    noneQuery p rows = true ↔ ¬ ∃ r ∈ rows, p r = true := by
  rw [noneQuery_eq_true_iff]
  simp

/-- A positive `exists` is monotone in the set of rows. -/
theorem existsQuery_mono {s t : Multiset R} (h : s ⊆ t) (hs : existsQuery p s = true) :
    existsQuery p t = true := by
  rw [existsQuery_eq_true_iff] at hs ⊢
  obtain ⟨r, hr, hp⟩ := hs
  exact ⟨r, h hr, hp⟩

variable [DecidableEq R]

theorem existsQuery_dedup (rows : Multiset R) : existsQuery p rows.dedup = existsQuery p rows :=
  supQuery_dedup p rows

theorem forallQuery_dedup (rows : Multiset R) : forallQuery p rows.dedup = forallQuery p rows :=
  infQuery_dedup p rows

theorem noneQuery_dedup (rows : Multiset R) : noneQuery p rows.dedup = noneQuery p rows := by
  rw [noneQuery, noneQuery, existsQuery_dedup]

end Predicate

/-! ## The `best` query -/

section Best

variable {R : Type u} {β : Type v} [LinearOrder β] (w : R → β)

/-- `best`: the largest weight of a row, `⊥` on the empty bag. The join-fold into `WithBot β`. -/
def bestQuery (rows : Multiset R) : WithBot β := supQuery (fun r => (w r : WithBot β)) rows

/-- A best row is present and no row weighs more: the matrix of the ∃∀ formula. -/
def IsBest (rows : Multiset R) (r : R) : Prop := r ∈ rows ∧ ∀ r' ∈ rows, w r' ≤ w r

theorem bestQuery_eq_bot_iff {rows : Multiset R} : bestQuery w rows = ⊥ ↔ rows = 0 := by
  constructor
  · intro h
    by_contra ne
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero ne
    have := le_supQuery (fun r => (w r : WithBot β)) hr
    rw [← bestQuery, h] at this
    exact WithBot.coe_ne_bot (le_bot_iff.mp this)
  · rintro rfl
    simp [bestQuery]

theorem bestQuery_le_iff {rows : Multiset R} {b : β} :
    bestQuery w rows ≤ b ↔ ∀ r ∈ rows, w r ≤ b := by
  simp [bestQuery, supQuery_le_iff]

theorem le_bestQuery {rows : Multiset R} {r : R} (h : r ∈ rows) : (w r : WithBot β) ≤ bestQuery w rows :=
  le_supQuery (fun r => (w r : WithBot β)) h

/-- A row is best exactly when it is present and its weight is the `best` value. -/
theorem isBest_iff_bestQuery {rows : Multiset R} {r : R} :
    IsBest w rows r ↔ r ∈ rows ∧ bestQuery w rows = w r := by
  constructor
  · rintro ⟨hr, hmax⟩
    exact ⟨hr, le_antisymm ((bestQuery_le_iff w).mpr hmax) (le_bestQuery w hr)⟩
  · rintro ⟨hr, hb⟩
    refine ⟨hr, fun r' hr' => ?_⟩
    have := le_bestQuery w hr'
    rw [hb] at this
    exact WithBot.coe_le_coe.mp this

/-- A nonempty bag has a best row: the argmax witness. -/
theorem exists_isBest {rows : Multiset R} (h : rows ≠ 0) : ∃ r, IsBest w rows r := by
  obtain ⟨r, hr, hmax⟩ := Multiset.exists_max_image w h
  exact ⟨r, hr, hmax⟩

/-- **`best` meets its specification, the ∃∀ formula.** -/
theorem bestQuery_eq_coe_iff {rows : Multiset R} {b : β} :
    bestQuery w rows = b ↔ ∃ r ∈ rows, w r = b ∧ ∀ r' ∈ rows, w r' ≤ w r := by
  constructor
  · intro hb
    have ne : rows ≠ 0 := by
      rintro rfl
      simp [bestQuery] at hb
    obtain ⟨r, hbest⟩ := exists_isBest w ne
    obtain ⟨hr, hval⟩ := (isBest_iff_bestQuery w).mp hbest
    exact ⟨r, hr, WithBot.coe_injective (hval.symm.trans hb), hbest.2⟩
  · rintro ⟨r, hr, rfl, hmax⟩
    exact ((isBest_iff_bestQuery w).mp ⟨hr, hmax⟩).2

theorem bestQuery_dedup [DecidableEq R] (rows : Multiset R) :
    bestQuery w rows.dedup = bestQuery w rows :=
  supQuery_dedup _ rows

/-- All best rows of a bag, with their multiplicities. -/
def bestRows (rows : Multiset R) : Multiset R := rows.filter fun r => bestQuery w rows = w r

theorem mem_bestRows {rows : Multiset R} {r : R} : r ∈ bestRows w rows ↔ IsBest w rows r := by
  rw [bestRows, Multiset.mem_filter, isBest_iff_bestQuery]

theorem bestRows_ne_zero {rows : Multiset R} (h : rows ≠ 0) : bestRows w rows ≠ 0 := by
  obtain ⟨r, hr⟩ := exists_isBest w h
  exact ne_zero_of_mem ((mem_bestRows w).mpr hr)

/-- The best rows of a bag depend only on which rows occur. -/
theorem mem_bestRows_dedup [DecidableEq R] {rows : Multiset R} {r : R} :
    r ∈ bestRows w rows.dedup ↔ r ∈ bestRows w rows := by
  simp only [mem_bestRows, IsBest, Multiset.mem_dedup]

/-- With a linear order on rows to break ties, the best row is a fold too: the supremum, in the
lexicographic order, of the pairs (weight, row). -/
def bestWitness [LinearOrder R] (rows : Multiset R) : WithBot (β ×ₗ R) :=
  supQuery (fun r => ((toLex (w r, r) : β ×ₗ R) : WithBot (β ×ₗ R))) rows

theorem bestWitness_eq_bot_iff [LinearOrder R] {rows : Multiset R} :
    bestWitness w rows = ⊥ ↔ rows = 0 := by
  constructor
  · intro h
    by_contra ne
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero ne
    have := le_supQuery (fun r => ((toLex (w r, r) : β ×ₗ R) : WithBot (β ×ₗ R))) hr
    rw [← bestWitness, h] at this
    exact WithBot.coe_ne_bot (le_bot_iff.mp this)
  · rintro rfl
    simp [bestWitness]

/-- **The witness fold returns a best row.** -/
theorem bestWitness_spec [LinearOrder R] {rows : Multiset R} (h : rows ≠ 0) :
    ∃ r, bestWitness w rows = ((toLex (w r, r) : β ×ₗ R) : WithBot (β ×ₗ R)) ∧ IsBest w rows r := by
  obtain ⟨r, hr, hmax⟩ := Multiset.exists_max_image (fun r => (toLex (w r, r) : β ×ₗ R)) h
  refine ⟨r, le_antisymm ?_
    (le_supQuery (fun r => ((toLex (w r, r) : β ×ₗ R) : WithBot (β ×ₗ R))) hr), hr,
    fun r' hr' => ?_⟩
  · exact (supQuery_le_iff _).mpr fun r' hr' => WithBot.coe_le_coe.mpr (hmax r' hr')
  · rcases (Prod.Lex.le_iff).mp (hmax r' hr') with lt | ⟨eq, -⟩
    · exact lt.le
    · exact eq.le

theorem bestWitness_dedup [LinearOrder R] (rows : Multiset R) :
    bestWitness w rows.dedup = bestWitness w rows :=
  supQuery_dedup _ rows

end Best

/-! ## Aggregate queries -/

section Aggregate

variable {R : Type u}

/-- `count`: the number of rows, with multiplicity. -/
def countQuery (rows : Multiset R) : ℕ := query (fun _ => 1) rows

/-- `sum`: the total of a weight over the rows, with multiplicity. -/
def sumQuery {M : Type v} [AddCommMonoid M] (w : R → M) (rows : Multiset R) : M := query w rows

/-- `parity`: the number of rows modulo two. -/
def parityQuery (rows : Multiset R) : ZMod 2 := query (fun _ => 1) rows

/-- The number of rows satisfying `p`, returned as data. -/
def countWhere (p : R → Prop) [DecidablePred p] (rows : Multiset R) : ℕ :=
  query (fun r => if p r then 1 else 0) rows

theorem countQuery_eq_card (rows : Multiset R) : countQuery rows = Multiset.card rows := by
  simp [countQuery, query]

theorem countWhere_eq_card_filter (p : R → Prop) [DecidablePred p] (rows : Multiset R) :
    countWhere p rows = Multiset.card (rows.filter p) := by
  induction rows using Multiset.induction_on with
  | empty => simp [countWhere]
  | cons a s ih =>
      rw [countWhere, query_cons, ← countWhere, ih, Multiset.filter_cons]
      split_ifs <;> simp [add_comm]

end Aggregate

/-! ## Separation: predicate queries do not see multiplicity -/

section Separation

variable {R : Type u} [DecidableEq R] {X : Type w}

/-- A function of bags of rows is dedup-invariant when removing duplicate rows never changes
it. -/
def DedupInvariant (F : Multiset R → X) : Prop := ∀ rows, F rows.dedup = F rows

/-- Dedup-invariance is dependence on the set of rows alone. -/
theorem dedupInvariant_iff (F : Multiset R → X) :
    DedupInvariant F ↔ ∀ s t : Multiset R, (∀ r, r ∈ s ↔ r ∈ t) → F s = F t := by
  constructor
  · intro hF s t h
    rw [← hF s, ← hF t, Multiset.dedup_ext.mpr h]
  · intro h rows
    exact h _ _ fun _ => Multiset.mem_dedup

theorem DedupInvariant.comp {F : Multiset R → X} (hF : DedupInvariant F) {Y : Type*}
    (g : X → Y) : DedupInvariant (g ∘ F) :=
  fun rows => by simp only [Function.comp, hF rows]

theorem dedupInvariant_query_of_idempotent {M : Type v} [AddCommMonoid M]
    (idem : ∀ m : M, m + m = m) (f : R → M) : DedupInvariant (query f) :=
  query_dedup_of_idempotent idem f

theorem dedupInvariant_supQuery {M : Type v} [SemilatticeSup M] [OrderBot M] (f : R → M) :
    DedupInvariant (supQuery f) :=
  supQuery_dedup f

theorem dedupInvariant_infQuery {M : Type v} [SemilatticeInf M] [OrderTop M] (f : R → M) :
    DedupInvariant (infQuery f) :=
  infQuery_dedup f

/-- A readout of a dedup-invariant function is dedup-invariant, so it computes nothing that is
not. -/
theorem not_computes_of_dedupInvariant {F : Multiset R → X} (hF : DedupInvariant F)
    {Y : Type*} {G : Multiset R → Y} (hG : ¬ DedupInvariant G) :
    ¬ ∃ g : X → Y, ∀ rows, g (F rows) = G rows := by
  rintro ⟨g, hg⟩
  exact hG fun rows => by rw [← hg, ← hg, hF]

private theorem dedup_pair (r : R) : ({r, r} : Multiset R).dedup = {r} := by
  rw [Multiset.insert_eq_cons, Multiset.dedup_cons_of_mem (Multiset.mem_singleton_self r),
    Multiset.dedup_singleton]

/-- `count` sees multiplicity. -/
theorem not_dedupInvariant_countQuery (r : R) : ¬ DedupInvariant (countQuery (R := R)) := by
  intro h
  have := h {r, r}
  rw [dedup_pair] at this
  simp [countQuery_eq_card] at this

/-- `parity` sees multiplicity. -/
theorem not_dedupInvariant_parityQuery (r : R) : ¬ DedupInvariant (parityQuery (R := R)) := by
  intro h
  have := h {r, r}
  rw [dedup_pair] at this
  simp [parityQuery] at this

/-- A `sum` of a weight that is nonzero somewhere sees multiplicity. -/
theorem not_dedupInvariant_sumQuery (w : R → ℕ) {r : R} (hr : w r ≠ 0) :
    ¬ DedupInvariant (sumQuery w) := by
  intro h
  have := h {r, r}
  rw [dedup_pair] at this
  simp [sumQuery] at this
  omega

/-- The count of the rows satisfying `p`, as data, sees multiplicity once some row satisfies
`p`. -/
theorem countWhere_not_dedupInvariant (p : R → Prop) [DecidablePred p] {r : R} (hr : p r) :
    ¬ DedupInvariant (countWhere p) := by
  intro h
  have := h {r, r}
  rw [dedup_pair] at this
  simp [countWhere, hr] at this

/-- **No predicate query computes `count`**, for any idempotent target and any readout. -/
theorem idempotent_query_not_count {M : Type v} [AddCommMonoid M] (idem : ∀ m : M, m + m = m)
    (f : R → M) (r : R) : ¬ ∃ g : M → ℕ, ∀ rows, g (query f rows) = countQuery rows :=
  not_computes_of_dedupInvariant (dedupInvariant_query_of_idempotent idem f)
    (not_dedupInvariant_countQuery r)

/-- **No predicate query computes `parity`**, for any idempotent target and any readout. -/
theorem idempotent_query_not_parity {M : Type v} [AddCommMonoid M] (idem : ∀ m : M, m + m = m)
    (f : R → M) (r : R) : ¬ ∃ g : M → ZMod 2, ∀ rows, g (query f rows) = parityQuery rows :=
  not_computes_of_dedupInvariant (dedupInvariant_query_of_idempotent idem f)
    (not_dedupInvariant_parityQuery r)

theorem supQuery_not_count {M : Type v} [SemilatticeSup M] [OrderBot M] (f : R → M) (r : R) :
    ¬ ∃ g : M → ℕ, ∀ rows, g (supQuery f rows) = countQuery rows :=
  not_computes_of_dedupInvariant (dedupInvariant_supQuery f) (not_dedupInvariant_countQuery r)

theorem supQuery_not_parity {M : Type v} [SemilatticeSup M] [OrderBot M] (f : R → M) (r : R) :
    ¬ ∃ g : M → ZMod 2, ∀ rows, g (supQuery f rows) = parityQuery rows :=
  not_computes_of_dedupInvariant (dedupInvariant_supQuery f) (not_dedupInvariant_parityQuery r)

theorem infQuery_not_count {M : Type v} [SemilatticeInf M] [OrderTop M] (f : R → M) (r : R) :
    ¬ ∃ g : M → ℕ, ∀ rows, g (infQuery f rows) = countQuery rows :=
  not_computes_of_dedupInvariant (dedupInvariant_infQuery f) (not_dedupInvariant_countQuery r)

theorem infQuery_not_parity {M : Type v} [SemilatticeInf M] [OrderTop M] (f : R → M) (r : R) :
    ¬ ∃ g : M → ZMod 2, ∀ rows, g (infQuery f rows) = parityQuery rows :=
  not_computes_of_dedupInvariant (dedupInvariant_infQuery f) (not_dedupInvariant_parityQuery r)

/-- The aggregates are genuine: `count` is a query into `ℕ`, whose addition is not idempotent. -/
example : ¬ ∀ m : ℕ, m + m = m := fun h => absurd (h 1) (by decide)

end Separation

/-! ## Basis: `forall`, `exists`, `none`, `best`, "at least `k`" -/

section Basis

variable {R : Type u}

/-- `exists` is `forall` under negation. -/
theorem existsQuery_eq_not_forallQuery (p : R → Bool) (rows : Multiset R) :
    existsQuery p rows = !forallQuery (fun r => !p r) rows := by
  rcases h : existsQuery p rows
  · rw [existsQuery_eq_false_iff] at h
    symm
    rw [Bool.not_eq_false', forallQuery_eq_true_iff]
    simpa using h
  · rw [existsQuery_eq_true_iff] at h
    obtain ⟨r, hr, hp⟩ := h
    symm
    rw [Bool.not_eq_true', ← Bool.not_eq_true, forallQuery_eq_true_iff]
    exact fun hall => by simpa [hp] using hall r hr

/-- `none` is `forall` of the negation. -/
theorem noneQuery_eq_forallQuery_not (p : R → Bool) (rows : Multiset R) :
    noneQuery p rows = forallQuery (fun r => !p r) rows := by
  rw [noneQuery, existsQuery_eq_not_forallQuery, Bool.not_not]

variable {β : Type v} [LinearOrder β] (w : R → β)

/-- A best row is a present row at which the `forall` query "no row weighs more" holds. -/
theorem isBest_iff_forallQuery {rows : Multiset R} {r : R} :
    IsBest w rows r ↔ r ∈ rows ∧ forallQuery (fun r' => decide (w r' ≤ w r)) rows = true := by
  rw [forallQuery_eq_true_iff]
  simp [IsBest]

/-- **`best` is the ∃∀ formula** written with the `exists` and `forall` queries. -/
theorem bestQuery_eq_coe_iff_existsQuery {rows : Multiset R} {b : β} :
    bestQuery w rows = b ↔
      existsQuery (fun r => decide (w r = b) && forallQuery (fun r' => decide (w r' ≤ w r)) rows)
        rows = true := by
  rw [bestQuery_eq_coe_iff, existsQuery_eq_true_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, forallQuery_eq_true_iff]

/-- A best row exists exactly when the bag is nonempty. -/
theorem existsQuery_isBest_iff {rows : Multiset R} :
    existsQuery (fun r => forallQuery (fun r' => decide (w r' ≤ w r)) rows) rows = true ↔
      rows ≠ 0 := by
  rw [existsQuery_eq_true_iff]
  constructor
  · rintro ⟨r, hr, -⟩
    exact ne_zero_of_mem hr
  · intro h
    obtain ⟨r, hr, hmax⟩ := exists_isBest w h
    exact ⟨r, hr, (forallQuery_eq_true_iff _).mpr fun r' hr' => by simpa using hmax r' hr'⟩

/-- **"At least `k`" is a statement with `k` distinct witnesses.** -/
theorem le_card_filter_iff_distinct_witnesses {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] (k : ℕ) :
    k ≤ (s.filter p).card ↔ ∃ x : Fin k → α, Function.Injective x ∧ ∀ i, x i ∈ s ∧ p (x i) := by
  classical
  constructor
  · intro hk
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin k) (β := s.filter p)
      (by simpa using hk)
    exact ⟨fun i => (e i).1, Subtype.val_injective.comp e.injective,
      fun i => Finset.mem_filter.mp (e i).2⟩
  · rintro ⟨x, hx, hmem⟩
    calc k = (Finset.univ.image x).card := by
            rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
      _ ≤ (s.filter p).card := Finset.card_le_card fun a ha => by
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
            exact Finset.mem_filter.mpr (hmem i)

variable [DecidableEq R]

/-- At least `k` distinct rows satisfy `p`. -/
def AtLeast (k : ℕ) (p : R → Prop) [DecidablePred p] (rows : Multiset R) : Prop :=
  k ≤ (rows.toFinset.filter p).card

theorem atLeast_iff_distinct_witnesses (k : ℕ) (p : R → Prop) [DecidablePred p]
    (rows : Multiset R) :
    AtLeast k p rows ↔ ∃ x : Fin k → R, Function.Injective x ∧ ∀ i, x i ∈ rows ∧ p (x i) := by
  rw [AtLeast, le_card_filter_iff_distinct_witnesses]
  simp only [Multiset.mem_toFinset]

/-- "At least `k` distinct rows satisfy `p`" depends only on the set of rows. -/
theorem atLeast_dedup (k : ℕ) (p : R → Prop) [DecidablePred p] (rows : Multiset R) :
    AtLeast k p rows.dedup ↔ AtLeast k p rows := by
  rw [AtLeast, AtLeast, Multiset.toFinset_dedup]

/-- Over a store of occurrences with identities, "at least `k` occurrences in a region" is a
statement with `k` distinct occurrence witnesses. -/
theorem atLeast_occurrences_iff {O : Type*} {L : Type*} (store : Finset O) (label : O → L)
    (region : L → Prop) [DecidablePred region] (k : ℕ) :
    k ≤ (store.filter fun o => region (label o)).card ↔
      ∃ x : Fin k → O, Function.Injective x ∧ ∀ i, x i ∈ store ∧ region (label (x i)) :=
  le_card_filter_iff_distinct_witnesses store _ k

end Basis

/-! ## Occurrences and answers -/

section Answers

variable {R : Type u} {A : Type v} [DecidableEq A] (bind : R → A)

/-- The answers of a bag under a binding map: the set of distinct bindings, a join-fold into
`Finset A`. -/
def answers (rows : Multiset R) : Finset A := supQuery (fun r => ({bind r} : Finset A)) rows

theorem answers_eq_toFinset (rows : Multiset R) : answers bind rows = (rows.map bind).toFinset := by
  induction rows using Multiset.induction_on with
  | empty => simp [answers]
  | cons a s ih =>
      rw [answers, supQuery_cons, ← answers, ih, Multiset.map_cons, Multiset.toFinset_cons,
        Finset.sup_eq_union, Finset.insert_eq]

theorem mem_answers {rows : Multiset R} {a : A} : a ∈ answers bind rows ↔ ∃ r ∈ rows, bind r = a := by
  rw [answers_eq_toFinset, Multiset.mem_toFinset, Multiset.mem_map]

/-- The number of answers: distinct bindings, not rows. -/
def countAnswers (rows : Multiset R) : ℕ := (answers bind rows).card

/-- The number of answers is a readout of a predicate query. -/
theorem countAnswers_eq_card_supQuery (rows : Multiset R) :
    countAnswers bind rows = (supQuery (fun r => ({bind r} : Finset A)) rows).card := rfl

theorem countAnswers_le_countQuery (rows : Multiset R) :
    countAnswers bind rows ≤ countQuery rows := by
  rw [countAnswers, answers_eq_toFinset, countQuery_eq_card, ← Multiset.card_map bind]
  exact Multiset.toFinset_card_le _

theorem countAnswers_eq_countQuery_iff (rows : Multiset R) :
    countAnswers bind rows = countQuery rows ↔ (rows.map bind).Nodup := by
  rw [countAnswers, answers_eq_toFinset, countQuery_eq_card, ← Multiset.card_map bind,
    Multiset.toFinset_card_eq_card_iff_nodup]

theorem countAnswers_dedup [DecidableEq R] (rows : Multiset R) :
    countAnswers bind rows.dedup = countAnswers bind rows := by
  rw [countAnswers, countAnswers, answers, answers, supQuery_dedup]

/-- **Occurrences and answers differ.** Two rows with one binding: two occurrences, one answer. -/
theorem occurrences_ne_answers :
    countQuery ({(1, 2), (1, 3)} : Multiset (ℕ × ℕ)) = 2 ∧
      countAnswers Prod.fst ({(1, 2), (1, 3)} : Multiset (ℕ × ℕ)) = 1 := by
  decide

/-- Two copies of one row: two occurrences, one answer, under the identity binding. -/
theorem occurrences_ne_answers_copies :
    countQuery ({1, 1} : Multiset ℕ) = 2 ∧ countAnswers id ({1, 1} : Multiset ℕ) = 1 := by
  decide

end Answers

end Mettapedia.GSLT.Core.RegionQueries

#print axioms Mettapedia.GSLT.Core.RegionQueries.collect_initial
#print axioms Mettapedia.GSLT.Core.RegionQueries.query_eq_queryHom_collect
#print axioms Mettapedia.GSLT.Core.RegionQueries.queryHom_restrict
#print axioms Mettapedia.GSLT.Core.RegionQueries.collectQuery_eq
#print axioms Mettapedia.GSLT.Core.RegionQueries.query_eq_sum_toFinset_of_idempotent
#print axioms Mettapedia.GSLT.Core.RegionQueries.query_dedup_of_idempotent
#print axioms Mettapedia.GSLT.Core.RegionQueries.supQuery_eq_finset_sup
#print axioms Mettapedia.GSLT.Core.RegionQueries.infQuery_eq_finset_inf
#print axioms Mettapedia.GSLT.Core.RegionQueries.supQuery_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.infQuery_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.existsQuery_eq_true_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.existsQuery_eq_false_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.forallQuery_eq_true_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.noneQuery_eq_true_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.noneQuery_eq_true_iff_not_exists
#print axioms Mettapedia.GSLT.Core.RegionQueries.existsQuery_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.forallQuery_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.noneQuery_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.existsQuery_mono
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestQuery_eq_bot_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestQuery_eq_coe_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.isBest_iff_bestQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.exists_isBest
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestQuery_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.mem_bestRows
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestRows_ne_zero
#print axioms Mettapedia.GSLT.Core.RegionQueries.mem_bestRows_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestWitness_eq_bot_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestWitness_spec
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestWitness_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.countQuery_eq_card
#print axioms Mettapedia.GSLT.Core.RegionQueries.countWhere_eq_card_filter
#print axioms Mettapedia.GSLT.Core.RegionQueries.dedupInvariant_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.not_computes_of_dedupInvariant
#print axioms Mettapedia.GSLT.Core.RegionQueries.not_dedupInvariant_countQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.not_dedupInvariant_parityQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.not_dedupInvariant_sumQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.countWhere_not_dedupInvariant
#print axioms Mettapedia.GSLT.Core.RegionQueries.idempotent_query_not_count
#print axioms Mettapedia.GSLT.Core.RegionQueries.idempotent_query_not_parity
#print axioms Mettapedia.GSLT.Core.RegionQueries.supQuery_not_count
#print axioms Mettapedia.GSLT.Core.RegionQueries.supQuery_not_parity
#print axioms Mettapedia.GSLT.Core.RegionQueries.infQuery_not_count
#print axioms Mettapedia.GSLT.Core.RegionQueries.infQuery_not_parity
#print axioms Mettapedia.GSLT.Core.RegionQueries.existsQuery_eq_not_forallQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.noneQuery_eq_forallQuery_not
#print axioms Mettapedia.GSLT.Core.RegionQueries.isBest_iff_forallQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.bestQuery_eq_coe_iff_existsQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.existsQuery_isBest_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.le_card_filter_iff_distinct_witnesses
#print axioms Mettapedia.GSLT.Core.RegionQueries.atLeast_iff_distinct_witnesses
#print axioms Mettapedia.GSLT.Core.RegionQueries.atLeast_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.atLeast_occurrences_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.answers_eq_toFinset
#print axioms Mettapedia.GSLT.Core.RegionQueries.mem_answers
#print axioms Mettapedia.GSLT.Core.RegionQueries.countAnswers_eq_card_supQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.countAnswers_le_countQuery
#print axioms Mettapedia.GSLT.Core.RegionQueries.countAnswers_eq_countQuery_iff
#print axioms Mettapedia.GSLT.Core.RegionQueries.countAnswers_dedup
#print axioms Mettapedia.GSLT.Core.RegionQueries.occurrences_ne_answers
#print axioms Mettapedia.GSLT.Core.RegionQueries.occurrences_ne_answers_copies
