import Mettapedia.GSLT.Dynamics.SymmetricAffineFold
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Bind

/-!
# Join aggregation by variable elimination

CeTTa stores the facts of a relation as an ordered list of rows, and duplicate rows are distinct
facts. The conjunction `(, (R $x $y) (S $y $z))` over binary relations enumerates, for each row
`(x, y)` of `R` in order, the rows `(y, z)` of `S` with the same `y`, in order (`join`). The path
`(, (R $a $b) (S $b $c) (T $c $d))` nests a third loop (`pathJoin`). An aggregate over such a
conjunction weighs each answer by a product of one weight per atom and sums over the answers,
with multiplicity. This module proves that the aggregate does not need the enumeration: each
relation is scanned once, and partial aggregates (messages) meet at the join keys. The join has
`|R| * |S|` answers when all rows share one key, while the messages visit `|R| + |S|` rows, and
`|R| + |S| + |T|` for the path.

Weights live in any `NonUnitalNonAssocSemiring`. Neither commutativity nor associativity of
multiplication is used, and products are formed in atom order. Counting in `ℕ`, sums in `ℤ`,
tropical semirings and dual numbers are instances. Variable elimination for factor graphs over
finite configuration spaces is `Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination`.
Here the factors are stored rows, ordered and with duplicates.

## What is proved

**Group sums.** `groupSum key w l y` sums `w` over the rows of `l` with key `y`, duplicates
included. `sum_map_eq_sum_groupSum` regroups a list aggregate by keys, over any finite key set
outside which the rows contribute `0`. `groupTable` computes every group sum in one ordered pass
(`groupTable_apply`).

**Two-way join.** Write `F y` for the group sum of `f` over `R` at `y` and `G y` for that of `g`
over `S`.
* `sum_join_eq_sum_keys` (main theorem): the aggregate of `f (x, y) * g (y, z)` over the join is
  `∑ y ∈ D, F y * G y` for every finite `D` containing the key of every answer. The keys of `R`
  (`sum_join_eq_sum_toFinset`), those of `S`, and their intersection all qualify.
* `sum_join_eq_sum_left`, `sum_join_eq_sum_right`: the streaming forms `∑ r ∈ R, f r * G r.2`
  and `∑ s ∈ S, F s.1 * g s`. `sum_join_eq_route` builds `G` with `groupTable`.
* `length_join`: the join size is `∑ y, countR y * countS y` over the keys of `R`, a statement
  about counts alone. `length_join_eq_sum_countP` is its streaming form.
* `groupSum_join`: grouping the answers by `z` gives `message F g S`, the message `R` passes
  through `S`. Selecting on `z` commutes with the join (`filter_join_eq_join_filter`).
* When all rows share one key, the join is the ordered product of the two relations and the
  main theorem is the product of the two aggregates, the two-factor case of
  `SemiringTraversal.weightSum_orderedProd`.

**Path join.** `sum_pathJoin_eq_sum_keys`: the aggregate of `f (a, b) * g (b, c) * h (c, d)`
over the path join is `∑ c ∈ D, m c * H c`. Here `m = message F g S`, so
`m c = ∑_{(b, c) ∈ S} F b * g (b, c)`, and `H c = ∑_{(c, d) ∈ T} h (c, d)`; `D` is any finite set
containing the `c` of every answer. `sum_pathJoin_eq_sum_message` streams over `T`,
`sum_pathJoin_eq_route` builds both messages with `groupTable`, and `length_pathJoin` counts
3-paths.

**Count and sum as one aggregate.** In the dual numbers `K[ε]` over a semiring `K`, a row
carrying the value `v` weighs `1 + v ε`. Along an answer the weights multiply by the product
rule `(1 + a ε) * (1 + b ε) = 1 + (a + b) ε` (`one_add_smul_eps_mul`), and over a list they sum
to `count + (∑ v) ε` (`sum_map_one_add_smul_eps`). The pair (count, sum) is therefore one
semiring aggregate, and elimination computes both components at once. A column carried by one
atom takes `v = 0`, weight `1`, on the others.
* `moment_join_eq_sum_keys`: with `1 + u ε` on the rows of `R` and `1 + w ε` on those of `S`,
  the join aggregate is the join size plus the sum of `u + w` over the answers times `ε`, and
  it factors through the join keys.
* `joinMoment R S u w` is that aggregate, factorized over the keys of `R`. It equals the
  enumerated sum of weight products (`joinMoment_eq_sum_join`), its `fst` is the join size and
  its `snd` the item sum (`fst_joinMoment`, `snd_joinMoment`). Per key it is
  `(countR y + sumR y ε) * (countS y + sumS y ε)` (`joinMoment_eq_sum_counts`), so the item sum
  is `∑ y, (countR y * sumS y + sumR y * countS y)` (`sum_join_item`), and a column carried by
  `R` sums to `∑ y, sumR y * countS y` (`sum_join_column`).
* `pathMoment R S T u v w` is the path aggregate by message passing, with `fst` the number of
  paths and `snd` the sum of `u + v + w` over them (`pathMoment_eq`, `fst_pathMoment`,
  `snd_pathMoment`).
* `foldall_translation_join`, `foldall_translation_pathJoin`, `sourceFold_addMulAdd_join`: the
  fold `acc ↦ acc + (c * item + d)` over the item values of the answers, in any order, returns
  `init + c * snd + d * fst` of the aggregate. They rest on
  `SymmetricAffineFold.foldall_add_mul_add` and on the recognized body
  `SymmetricAffineFold.addMulAdd`.

**Enumeration order.** `join` is `R`-major, and `joinRightMajor` enumerates the same join
`S`-major. They are permutations of each other (`join_perm_joinRightMajor`), so commutative
aggregates and folds whose coefficients pairwise commute, translations in particular, agree on
them (`sum_map_join_eq_joinRightMajor`, `foldall_join_eq_joinRightMajor`,
`foldall_join_eq_joinRightMajor_of_translations`). The answer streams themselves differ.

## Controls

* `join_order_control` lists both enumerations of a four-answer join.
* `twoAccPlusItem_sees_join_order` (negative): the admitted body `2 * acc + item`, which fails the
  reordering admission, folds the `x` column to `18` `R`-major and to `20` `S`-major.
  `addMulAdd_ignores_join_order`: the translation `acc + (3 * item + 1)` gives `22` in both.
* On a graph whose edge `0 → 1` is stored twice: `two_paths_control` (8 two-paths, enumerated
  and factorized), `three_paths_control` (10 three-paths, enumerated, streamed and keyed),
  `two_path_source_sum_control` (source-vertex sum `6`, enumerated and factorized),
  `two_path_moment_control` (one dual aggregate with `fst = 8` and `snd = 6`),
  `two_path_endpoint_sum_control` (columns on both atoms: `x + z` sums to `21`),
  `three_path_moment_control` (10 three-paths with `a + d` summing to `28`) and
  `two_path_fold_control` (a translation fold, enumerated and read from the aggregate).

## What is not covered

* **Cyclic joins.** In the triangle `(, (R $a $b) (S $b $c) (T $c $a))`, eliminating one
  variable leaves a factor on two variables, so messages over single keys do not suffice.
  Worst-case optimal join algorithms (generic join, leapfrog triejoin) are the known route. They
  are not formalized here.
* **Other acyclic shapes.** Only the two-atom join and the three-atom path are stated. Longer
  paths and trees admit the same elimination, message by message, but are not stated.
* **Non-factorizing weights.** The weight of an answer must be a product of one factor per atom.
  An item mixing the variables of two atoms multiplicatively, such as `(* $x $z)`, is not
  covered. Sums of per-atom columns are (`moment_join_eq_sum_keys`, `pathMoment_eq`).
* **Product aggregates.** Folds that multiply by the item, `acc ↦ item * acc`, are not stated for
  joins. Their value is a product of per-row values raised to counts from the other side. The
  same holds for the other folds that are not translations.
* **Order-sensitive consumers.** The factorized routes compute bag aggregates only. A fold that
  is not a translation, a trajectory, or the first answer sees the enumeration order
  (`twoAccPlusItem_sees_join_order`) and needs the ordered answer stream.
* **Cost.** The route theorems exhibit one pass per relation plus key tables. No operation
  count, hashing cost or memory bound is proved.
* **Machine arithmetic.** All laws are exact. Counts and sums over large joins need overflow
  guards in the native realization.
* **Atom shapes.** Relations are binary and share one variable. Constants or repeated variables
  inside an atom are selections on the stored rows before the join. A key of several variables
  is covered only by taking `Y` to be a product type.

## Mapping to CeTTa's native join aggregation

For an aggregate over `(, (R $x $y) (S $y $z))` with per-atom weights, the runtime may scan `S`
once into a table keyed by `y` (`groupTable Prod.fst g S`), then scan `R` once, multiplying each
row's weight by the table entry at its `y` (`sum_join_eq_route`). For the path, each relation's
table carries the message to the next join variable, `R` to `b` and `S` to `c`, and a final scan
of `T` closes the sum (`sum_pathJoin_eq_route`). Counting uses weight `1`. A `foldall` over the
conjunction whose compiled step is the translation `acc + (c * item + d)`, with the item a
variable of one atom or a sum of such variables, may take its value from one dual-number
aggregate as `init + c * snd + d * fst` (`sourceFold_addMulAdd_join`,
`foldall_translation_pathJoin`). The messages then carry pairs (count, sum), multiplied by the
product rule. Folds that fail the reordering admission need the ordered answer stream.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.JoinAggregation

open Mettapedia.Algebra Mettapedia.GSLT.Dynamics.AffineFoldCompilation
open scoped DualNumber

variable {α β γ X Y Z W K : Type*}

/-! ## Nested loops -/

section NestedLoops

/-- Aggregating a `flatMap` aggregates each block. -/
theorem sum_map_flatMap [AddMonoid K] (l : List α) (F : α → List β) (w : β → K) :
    ((l.flatMap F).map w).sum = (l.map fun a => ((F a).map w).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A filtered map is a nested loop whose body emits at most one row. -/
theorem map_filter_eq_flatMap (l : List α) (p : α → Bool) (φ : α → β) :
    (l.filter p).map φ = l.flatMap fun a => if p a then [φ a] else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

/-- Exchanging two nested loops permutes the emitted rows. -/
theorem flatMap_flatMap_perm (A : List α) (B : List β) (F : α → β → List γ) :
    (A.flatMap fun a => B.flatMap fun b => F a b).Perm
      (B.flatMap fun b => A.flatMap fun a => F a b) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_bind, ← Multiset.coe_bind]
  simp only [← Multiset.coe_bind]
  exact Multiset.bind_bind _ _

end NestedLoops

/-! ## Group sums -/

section GroupSum

variable [DecidableEq Y] [AddCommMonoid K]

/-- The aggregate of `w` over the rows of `l` whose key is `y`, counted with multiplicity. -/
def groupSum (key : α → Y) (w : α → K) (l : List α) (y : Y) : K :=
  ((l.filter fun a => key a = y).map w).sum

@[simp] theorem groupSum_nil (key : α → Y) (w : α → K) (y : Y) :
    groupSum key w [] y = 0 := rfl

@[simp] theorem groupSum_zero (key : α → Y) (l : List α) (y : Y) :
    groupSum key (fun _ => (0 : K)) l y = 0 := by
  simp [groupSum]

theorem groupSum_cons (key : α → Y) (w : α → K) (a : α) (l : List α) (y : Y) :
    groupSum key w (a :: l) y = (if key a = y then w a else 0) + groupSum key w l y := by
  by_cases h : key a = y <;> simp [groupSum, h]

/-- A key carried by no row has group sum `0`. -/
theorem groupSum_eq_zero {key : α → Y} (w : α → K) {l : List α} {y : Y}
    (h : ∀ a ∈ l, key a ≠ y) : groupSum key w l y = 0 := by
  rw [groupSum, List.filter_eq_nil_iff.2 fun a ha => by simpa using h a ha]
  rfl

/-- **Regrouping.** A list aggregate is the sum of its group sums over any finite set of keys
outside which every row contributes `0`. -/
theorem sum_map_eq_sum_groupSum (key : α → Y) (u : α → K) {l : List α} {D : Finset Y}
    (hD : ∀ a ∈ l, key a ∉ D → u a = 0) :
    (l.map u).sum = ∑ y ∈ D, groupSum key u l y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih fun b hb => hD b (List.mem_cons_of_mem a hb)]
    simp only [groupSum_cons, Finset.sum_add_distrib, Finset.sum_ite_eq]
    by_cases ha : key a ∈ D
    · rw [if_pos ha]
    · rw [if_neg ha, hD a List.mem_cons_self ha]

/-- Counting: with weight `1`, a group sum is the number of rows with that key. -/
theorem groupSum_one {K : Type*} [AddCommMonoidWithOne K] (key : α → Y) (l : List α) (y : Y) :
    groupSum key (fun _ => (1 : K)) l y = ((l.countP fun a => key a = y : ℕ) : K) := by
  simp [groupSum, List.countP_eq_length_filter]

/-- One ordered pass over the rows, adding each row's weight at its key: a table of all group
sums, `0` at absent keys. -/
def groupTable (key : α → Y) (w : α → K) (l : List α) : Y → K :=
  l.foldl (fun t a => Function.update t (key a) (t (key a) + w a)) 0

/-- The one-pass table holds every group sum. -/
theorem groupTable_apply (key : α → Y) (w : α → K) (l : List α) (y : Y) :
    groupTable key w l y = groupSum key w l y := by
  suffices h : ∀ t : Y → K,
      (l.foldl (fun t a => Function.update t (key a) (t (key a) + w a)) t) y =
        t y + groupSum key w l y by
    simpa [groupTable] using h 0
  induction l with
  | nil => intro t; simp
  | cons a l ih =>
    intro t
    rw [List.foldl_cons, ih, groupSum_cons]
    by_cases h : key a = y
    · subst h
      simp [add_assoc]
    · simp [Function.update_of_ne (Ne.symm h), h]

end GroupSum

section GroupSumMul

variable [DecidableEq Y] [NonUnitalNonAssocSemiring K]

/-- A right factor that depends only on the key leaves the group. -/
theorem groupSum_mul_right (key : α → Y) (w : α → K) (c : Y → K) (l : List α) (y : Y) :
    groupSum key (fun a => w a * c (key a)) l y = groupSum key w l y * c y := by
  rw [groupSum, groupSum, ← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  rw [of_decide_eq_true (List.mem_filter.1 ha).2]

/-- A left factor that depends only on the key leaves the group. -/
theorem groupSum_mul_left (key : α → Y) (w : α → K) (c : Y → K) (l : List α) (y : Y) :
    groupSum key (fun a => c (key a) * w a) l y = c y * groupSum key w l y := by
  rw [groupSum, groupSum, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  rw [of_decide_eq_true (List.mem_filter.1 ha).2]

end GroupSumMul

/-! ## The two-way join -/

section Join

variable [DecidableEq Y]

/-- `(, (R $x $y) (S $y $z))` over stored rows, `R`-major: for each row `(x, y)` of `R` in order,
the rows `(y, z)` of `S` in order. Duplicate rows give duplicate answers. -/
def join (R : List (X × Y)) (S : List (Y × Z)) : List (X × Y × Z) :=
  R.flatMap fun r => (S.filter fun s => s.1 = r.2).map fun s => (r.1, r.2, s.2)

/-- The same join enumerated `S`-major: for each row of `S` in order, the matching rows of `R`
in order. -/
def joinRightMajor (R : List (X × Y)) (S : List (Y × Z)) : List (X × Y × Z) :=
  S.flatMap fun s => (R.filter fun r => r.2 = s.1).map fun r => (r.1, r.2, s.2)

/-- An answer of the join is a row of `R` and a row of `S` that agree on `y`. -/
theorem mem_join {R : List (X × Y)} {S : List (Y × Z)} {x : X} {y : Y} {z : Z} :
    (x, y, z) ∈ join R S ↔ (x, y) ∈ R ∧ (y, z) ∈ S := by
  simp only [join, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨r, hr, s, ⟨hs, hsr⟩, rfl, rfl, rfl⟩
    exact ⟨hr, by rw [← hsr]; exact hs⟩
  · rintro ⟨hxy, hyz⟩
    exact ⟨(x, y), hxy, (y, z), ⟨hyz, rfl⟩, rfl, rfl, rfl⟩

/-- The two enumerations of a join are permutations of each other. -/
theorem join_perm_joinRightMajor (R : List (X × Y)) (S : List (Y × Z)) :
    (join R S).Perm (joinRightMajor R S) := by
  have hc : ∀ (r : X × Y) (s : Y × Z), decide (s.1 = r.2) = decide (r.2 = s.1) :=
    fun _ _ => decide_eq_decide.2 eq_comm
  simp only [join, joinRightMajor, map_filter_eq_flatMap, hc]
  exact flatMap_flatMap_perm R S _

/-- Selecting on the last variable commutes with the join. -/
theorem filter_join_eq_join_filter (R : List (X × Y)) (S : List (Y × Z)) (q : Z → Bool) :
    (join R S).filter (fun t => q t.2.2) = join R (S.filter fun s => q s.2) := by
  simp only [join, List.filter_flatMap, List.filter_map, List.filter_filter]
  congr 1
  funext r
  congr 1
  apply List.filter_congr
  intro s _
  simp [Function.comp, Bool.and_comm]

end Join

section JoinAggregate

variable [DecidableEq Y] [NonUnitalNonAssocSemiring K]

/-- The join aggregate, streaming over `R`: the `S` side is eliminated into its group sums. -/
theorem sum_join_eq_sum_left (R : List (X × Y)) (S : List (Y × Z)) (f : X × Y → K)
    (g : Y × Z → K) :
    ((join R S).map fun t => f (t.1, t.2.1) * g (t.2.1, t.2.2)).sum =
      (R.map fun r => f r * groupSum Prod.fst g S r.2).sum := by
  rw [join, sum_map_flatMap]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  rw [groupSum, ← List.sum_map_mul_left, List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  have hsr : s.1 = r.2 := of_decide_eq_true (List.mem_filter.1 hs).2
  have hs' : (r.2, s.2) = s := by rw [← hsr]
  simp only [Function.comp_apply, Prod.mk.eta, hs']

/-- The join aggregate, streaming over `S`: the `R` side is eliminated into its group sums. -/
theorem sum_join_eq_sum_right (R : List (X × Y)) (S : List (Y × Z)) (f : X × Y → K)
    (g : Y × Z → K) :
    ((join R S).map fun t => f (t.1, t.2.1) * g (t.2.1, t.2.2)).sum =
      (S.map fun s => groupSum Prod.snd f R s.1 * g s).sum := by
  rw [((join_perm_joinRightMajor R S).map _).sum_eq, joinRightMajor, sum_map_flatMap]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  rw [groupSum, ← List.sum_map_mul_right, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  have hrs : r.2 = s.1 := of_decide_eq_true (List.mem_filter.1 hr).2
  have hs' : (r.2, s.2) = s := by rw [hrs]
  simp only [Function.comp_apply, Prod.mk.eta, hs']

/-- **Two-way variable elimination.** The aggregate over the join is the sum over the join keys
of the products of the per-side group sums. Any finite key set containing the key of every
answer may be used. -/
theorem sum_join_eq_sum_keys (R : List (X × Y)) (S : List (Y × Z)) (f : X × Y → K)
    (g : Y × Z → K) {D : Finset Y} (hD : ∀ x y z, (x, y) ∈ R → (y, z) ∈ S → y ∈ D) :
    ((join R S).map fun t => f (t.1, t.2.1) * g (t.2.1, t.2.2)).sum =
      ∑ y ∈ D, groupSum Prod.snd f R y * groupSum Prod.fst g S y := by
  rw [sum_join_eq_sum_left, sum_map_eq_sum_groupSum Prod.snd _ fun r hr hrD => ?_]
  · exact Finset.sum_congr rfl fun y _ => groupSum_mul_right Prod.snd f _ R y
  · refine (congrArg (f r * ·) (groupSum_eq_zero g fun s hs hsr => hrD ?_)).trans (mul_zero _)
    have hs' : (r.2, s.2) = s := by rw [← hsr]
    exact hD r.1 r.2 s.2 (by simpa using hr) (by rw [hs']; exact hs)

/-- **Two-way variable elimination** over the keys of `R`. -/
theorem sum_join_eq_sum_toFinset (R : List (X × Y)) (S : List (Y × Z)) (f : X × Y → K)
    (g : Y × Z → K) :
    ((join R S).map fun t => f (t.1, t.2.1) * g (t.2.1, t.2.2)).sum =
      ∑ y ∈ (R.map Prod.snd).toFinset, groupSum Prod.snd f R y * groupSum Prod.fst g S y :=
  sum_join_eq_sum_keys R S f g fun x y _ hxy _ =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨(x, y), hxy, rfl⟩)

/-- The executable two-way route: one pass over `S` builds the table, one pass over `R`
reads it. -/
theorem sum_join_eq_route (R : List (X × Y)) (S : List (Y × Z)) (f : X × Y → K)
    (g : Y × Z → K) :
    ((join R S).map fun t => f (t.1, t.2.1) * g (t.2.1, t.2.2)).sum =
      (R.map fun r => f r * groupTable Prod.fst g S r.2).sum := by
  simp only [groupTable_apply]
  exact sum_join_eq_sum_left R S f g

end JoinAggregate

/-! ## Counting -/

section Count

variable [DecidableEq Y]

/-- The join size, by elimination over any key set containing the key of every answer. -/
theorem length_join_eq_sum_keys (R : List (X × Y)) (S : List (Y × Z)) {D : Finset Y}
    (hD : ∀ x y z, (x, y) ∈ R → (y, z) ∈ S → y ∈ D) :
    (join R S).length =
      ∑ y ∈ D, (R.countP fun r => r.2 = y) * (S.countP fun s => s.1 = y) := by
  have h := sum_join_eq_sum_keys R S (fun _ => (1 : ℕ)) (fun _ => 1) hD
  simpa [groupSum_one] using h

/-- **The join size** is the sum, over the keys of `R`, of the products of the per-key counts. -/
theorem length_join (R : List (X × Y)) (S : List (Y × Z)) :
    (join R S).length = ∑ y ∈ (R.map Prod.snd).toFinset,
      (R.countP fun r => r.2 = y) * (S.countP fun s => s.1 = y) :=
  length_join_eq_sum_keys R S fun x y _ hxy _ =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨(x, y), hxy, rfl⟩)

/-- The join size, streaming over `R` with the key counts of `S`. -/
theorem length_join_eq_sum_countP (R : List (X × Y)) (S : List (Y × Z)) :
    (join R S).length = (R.map fun r => S.countP fun s => s.1 = r.2).sum := by
  have h := sum_join_eq_sum_left R S (fun _ => (1 : ℕ)) (fun _ => 1)
  simpa [groupSum_one] using h

end Count

/-! ## Messages -/

section Message

variable [DecidableEq Z] [NonUnitalNonAssocSemiring K]

/-- The message a weighted relation passes forward: at `z`, the sum of `μ y * g (y, z)` over the
rows `(y, z)` of `S`, with multiplicity. -/
def message (μ : Y → K) (g : Y × Z → K) (S : List (Y × Z)) (z : Z) : K :=
  groupSum Prod.snd (fun s => μ s.1 * g s) S z

/-- **The message is the grouped join aggregate.** Grouping the answers of `R ⋈ S` by their
last variable gives the message that the group sums of `R` pass through `S`. -/
theorem groupSum_join [DecidableEq Y] (R : List (X × Y)) (S : List (Y × Z)) (f : X × Y → K)
    (g : Y × Z → K) (z : Z) :
    groupSum (fun t : X × Y × Z => t.2.2) (fun t => f (t.1, t.2.1) * g (t.2.1, t.2.2))
        (join R S) z =
      message (groupSum Prod.snd f R) g S z := by
  rw [groupSum, filter_join_eq_join_filter R S fun c => decide (c = z), sum_join_eq_sum_right]
  rfl

end Message

/-! ## The three-way path join -/

section PathJoin

variable [DecidableEq Y] [DecidableEq Z]

/-- `(, (R $a $b) (S $b $c) (T $c $d))` over stored rows, in conjunct order: for each row of `R`,
each matching row of `S`, each matching row of `T`. -/
def pathJoin (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) :
    List (X × Y × Z × W) :=
  R.flatMap fun r => (S.filter fun s => s.1 = r.2).flatMap fun s =>
    (T.filter fun t => t.1 = s.2).map fun t => (r.1, r.2, s.2, t.2)

/-- The path join extends each answer of the two-way join, in order. -/
theorem pathJoin_eq_flatMap_join (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) :
    pathJoin R S T = (join R S).flatMap fun q =>
      (T.filter fun t => t.1 = q.2.2).map fun t => (q.1, q.2.1, q.2.2, t.2) := by
  simp only [pathJoin, join, List.flatMap_assoc, List.flatMap_map]

section Aggregate

variable [NonUnitalNonAssocSemiring K]

/-- **Three-way variable elimination.** The aggregate over the path join is the sum over `c` of
the message that `R` passes through `S` times the group sum of `T`. Any finite set containing
the `c` of every answer may be used. -/
theorem sum_pathJoin_eq_sum_keys (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W))
    (f : X × Y → K) (g : Y × Z → K) (h : Z × W → K) {D : Finset Z}
    (hD : ∀ x y z w, (x, y) ∈ R → (y, z) ∈ S → (z, w) ∈ T → z ∈ D) :
    ((pathJoin R S T).map fun q =>
        f (q.1, q.2.1) * g (q.2.1, q.2.2.1) * h (q.2.2.1, q.2.2.2)).sum =
      ∑ z ∈ D, message (groupSum Prod.snd f R) g S z * groupSum Prod.fst h T z := by
  rw [pathJoin_eq_flatMap_join, sum_map_flatMap]
  have hrow : ∀ q : X × Y × Z,
      ((((T.filter fun t => t.1 = q.2.2).map fun t => (q.1, q.2.1, q.2.2, t.2)).map fun q =>
          f (q.1, q.2.1) * g (q.2.1, q.2.2.1) * h (q.2.2.1, q.2.2.2)).sum) =
        f (q.1, q.2.1) * g (q.2.1, q.2.2) * groupSum Prod.fst h T q.2.2 := by
    intro q
    rw [groupSum, ← List.sum_map_mul_left, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have htq : t.1 = q.2.2 := of_decide_eq_true (List.mem_filter.1 ht).2
    have ht' : (q.2.2, t.2) = t := by rw [← htq]
    simp only [Function.comp_apply, ht']
  rw [List.map_congr_left fun q _ => hrow q,
    sum_map_eq_sum_groupSum (fun q : X × Y × Z => q.2.2) _ fun q hq hqD => ?_]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [groupSum_mul_right (fun q : X × Y × Z => q.2.2)
      (fun q => f (q.1, q.2.1) * g (q.2.1, q.2.2)) (groupSum Prod.fst h T), groupSum_join]
  · refine (congrArg (_ * ·) (groupSum_eq_zero h fun t ht htq => hqD ?_)).trans (mul_zero _)
    obtain ⟨x, y, z⟩ := q
    have ht' : (z, t.2) = t := by rw [show z = t.1 from htq.symm]
    exact hD x y z t.2 (mem_join.1 hq).1 (mem_join.1 hq).2 (by rw [ht']; exact ht)

/-- The form streaming over `T`: once the message is built, one pass over `T`. -/
theorem sum_pathJoin_eq_sum_message (R : List (X × Y)) (S : List (Y × Z))
    (T : List (Z × W)) (f : X × Y → K) (g : Y × Z → K) (h : Z × W → K) :
    ((pathJoin R S T).map fun q =>
        f (q.1, q.2.1) * g (q.2.1, q.2.2.1) * h (q.2.2.1, q.2.2.2)).sum =
      (T.map fun t => message (groupSum Prod.snd f R) g S t.1 * h t).sum := by
  have hT : ∀ x y z w, (x, y) ∈ R → (y, z) ∈ S → (z, w) ∈ T →
      z ∈ (T.map Prod.fst).toFinset :=
    fun _ _ z w _ _ hzw => List.mem_toFinset.2 (List.mem_map.2 ⟨(z, w), hzw, rfl⟩)
  rw [sum_pathJoin_eq_sum_keys R S T f g h hT,
    sum_map_eq_sum_groupSum Prod.fst _ fun t ht htD =>
      absurd (List.mem_toFinset.2 (List.mem_map.2 ⟨t, ht, rfl⟩)) htD]
  exact Finset.sum_congr rfl fun z _ => (groupSum_mul_left Prod.fst h _ T z).symm

/-- The executable three-way route: one ordered pass over each relation. -/
theorem sum_pathJoin_eq_route (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W))
    (f : X × Y → K) (g : Y × Z → K) (h : Z × W → K) :
    ((pathJoin R S T).map fun q =>
        f (q.1, q.2.1) * g (q.2.1, q.2.2.1) * h (q.2.2.1, q.2.2.2)).sum =
      (T.map fun t =>
        groupTable Prod.snd (fun s => groupTable Prod.snd f R s.1 * g s) S t.1 * h t).sum := by
  simp only [groupTable_apply]
  exact sum_pathJoin_eq_sum_message R S T f g h

end Aggregate

/-- The number of 3-paths: for each row of `T`, the number of 2-paths through `R` and `S` that
end at its first vertex. -/
theorem length_pathJoin (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) :
    (pathJoin R S T).length =
      (T.map fun t => groupSum Prod.snd (fun s => R.countP fun r => r.2 = s.1) S t.1).sum := by
  have h := sum_pathJoin_eq_sum_message R S T (fun _ => (1 : ℕ)) (fun _ => 1) (fun _ => 1)
  simpa [message, groupSum_one] using h

end PathJoin

/-! ## Count and sum as one aggregate -/

section Moments

variable [Semiring K]

/-- Joining two answers multiplies their dual weights, and the carried values add: `(count, sum)`
pairs multiply by the product rule. -/
theorem one_add_smul_eps_mul (a b : K) :
    ((1 : K[ε]) + a • ε) * (1 + b • ε) = 1 + (a + b) • ε := by
  ext <;> simp [add_comm]

/-- Summing `1 + v ε` over a list gives its length plus its value sum times `ε`. -/
theorem sum_map_one_add_smul_eps (l : List α) (v : α → K) :
    (l.map fun a => (1 : K[ε]) + v a • ε).sum = (l.length : K[ε]) + (l.map v).sum • ε := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_succ, add_smul]
    abel

variable [DecidableEq Y]

/-- Per key, the dual group sum of a relation carrying `v` is its count plus its value sum
times `ε`. -/
theorem groupSum_one_add_smul_eps (key : α → Y) (v : α → K) (l : List α) (y : Y) :
    groupSum key (fun a => (1 : K[ε]) + v a • ε) l y =
      ((l.countP fun a => key a = y : ℕ) : K[ε]) + groupSum key v l y • ε := by
  rw [groupSum, sum_map_one_add_smul_eps, List.countP_eq_length_filter, groupSum]

/-- **Count and sum in one aggregate.** With `1 + u ε` on the rows of `R` and `1 + w ε` on those
of `S`, the join aggregate is the join size plus the sum of `u + w` over the answers times `ε`,
and it factors through the join keys. -/
theorem moment_join_eq_sum_keys (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K)
    (w : Y × Z → K) {D : Finset Y} (hD : ∀ x y z, (x, y) ∈ R → (y, z) ∈ S → y ∈ D) :
    ((join R S).length : K[ε]) +
        ((join R S).map fun t => u (t.1, t.2.1) + w (t.2.1, t.2.2)).sum • ε =
      ∑ y ∈ D, groupSum Prod.snd (fun r => 1 + u r • ε) R y *
        groupSum Prod.fst (fun s => 1 + w s • ε) S y := by
  rw [← sum_join_eq_sum_keys R S _ _ hD, ← sum_map_one_add_smul_eps]
  simp only [one_add_smul_eps_mul]

/-- The `(count, sum)` of `join R S` for the item `u (x, y) + w (y, z)`, computed from per-key
messages: the rows of `R` weigh `1 + u ε` and the rows of `S` weigh `1 + w ε`. For a column
carried by one relation the other function is `0`, and that relation's rows weigh `1`. -/
def joinMoment (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K) (w : Y × Z → K) : K[ε] :=
  ∑ y ∈ (R.map Prod.snd).toFinset,
    groupSum Prod.snd (fun r => 1 + u r • ε) R y * groupSum Prod.fst (fun s => 1 + w s • ε) S y

/-- The factorized aggregate is the enumerated one: the sum over the answers of the products of
the row weights. -/
theorem joinMoment_eq_sum_join (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K)
    (w : Y × Z → K) :
    joinMoment R S u w =
      ((join R S).map fun t =>
        ((1 : K[ε]) + u (t.1, t.2.1) • ε) * (1 + w (t.2.1, t.2.2) • ε)).sum :=
  (sum_join_eq_sum_toFinset R S _ _).symm

/-- The aggregate is the join size plus the item sum times `ε`. -/
theorem joinMoment_eq (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K) (w : Y × Z → K) :
    joinMoment R S u w = ((join R S).length : K[ε]) +
      ((join R S).map fun t => u (t.1, t.2.1) + w (t.2.1, t.2.2)).sum • ε :=
  (moment_join_eq_sum_keys R S u w fun x y _ hxy _ =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨(x, y), hxy, rfl⟩)).symm

/-- The first component of the aggregate is the join size. -/
theorem fst_joinMoment (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K) (w : Y × Z → K) :
    (joinMoment R S u w).fst = (join R S).length := by
  simp [joinMoment_eq]

/-- The second component of the aggregate is the item sum over the join. -/
theorem snd_joinMoment (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K) (w : Y × Z → K) :
    (joinMoment R S u w).snd = ((join R S).map fun t => u (t.1, t.2.1) + w (t.2.1, t.2.2)).sum := by
  simp [joinMoment_eq]

/-- Per key, the message is the product of the two sides' `(count, sum)`. -/
theorem joinMoment_eq_sum_counts (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K)
    (w : Y × Z → K) :
    joinMoment R S u w = ∑ y ∈ (R.map Prod.snd).toFinset,
      (((R.countP fun r => r.2 = y : ℕ) : K[ε]) + groupSum Prod.snd u R y • ε) *
        (((S.countP fun s => s.1 = y : ℕ) : K[ε]) + groupSum Prod.fst w S y • ε) := by
  simp only [joinMoment, groupSum_one_add_smul_eps]

/-- **The item sum by elimination**: per key, the count of `R` times the value sum of `S` plus the
value sum of `R` times the count of `S`. -/
theorem sum_join_item (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K) (w : Y × Z → K) :
    ((join R S).map fun t => u (t.1, t.2.1) + w (t.2.1, t.2.2)).sum =
      ∑ y ∈ (R.map Prod.snd).toFinset,
        (((R.countP fun r => r.2 = y : ℕ) : K) * groupSum Prod.fst w S y +
          groupSum Prod.snd u R y * ((S.countP fun s => s.1 = y : ℕ) : K)) := by
  rw [← snd_joinMoment, joinMoment_eq_sum_counts, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

/-- **A column carried by `R`**: its sum over the join is, per key, its sum over `R` times the
count of `S`. -/
theorem sum_join_column (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K) :
    ((join R S).map fun t => u (t.1, t.2.1)).sum =
      ∑ y ∈ (R.map Prod.snd).toFinset,
        groupSum Prod.snd u R y * ((S.countP fun s => s.1 = y : ℕ) : K) := by
  simpa using sum_join_item R S u fun _ => 0

variable [DecidableEq Z]

/-- The `(count, sum)` of `pathJoin R S T` for the item `u (a, b) + v (b, c) + w (c, d)`, computed
by message passing: the rows weigh `1 + u ε`, `1 + v ε` and `1 + w ε`. -/
def pathMoment (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) (u : X × Y → K)
    (v : Y × Z → K) (w : Z × W → K) : K[ε] :=
  ∑ z ∈ (T.map Prod.fst).toFinset,
    message (groupSum Prod.snd (fun r => 1 + u r • ε) R) (fun s => 1 + v s • ε) S z *
      groupSum Prod.fst (fun t => 1 + w t • ε) T z

/-- The path aggregate is the number of paths plus the item sum times `ε`. -/
theorem pathMoment_eq (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) (u : X × Y → K)
    (v : Y × Z → K) (w : Z × W → K) :
    pathMoment R S T u v w = ((pathJoin R S T).length : K[ε]) +
      ((pathJoin R S T).map fun q =>
        u (q.1, q.2.1) + v (q.2.1, q.2.2.1) + w (q.2.2.1, q.2.2.2)).sum • ε := by
  rw [pathMoment, ← sum_pathJoin_eq_sum_keys R S T _ _ _ fun _ _ c d _ _ hcd =>
      List.mem_toFinset.2 (List.mem_map.2 ⟨(c, d), hcd, rfl⟩), ← sum_map_one_add_smul_eps]
  simp only [one_add_smul_eps_mul]

/-- The first component of the path aggregate is the number of paths. -/
theorem fst_pathMoment (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) (u : X × Y → K)
    (v : Y × Z → K) (w : Z × W → K) :
    (pathMoment R S T u v w).fst = (pathJoin R S T).length := by
  simp [pathMoment_eq]

/-- The second component of the path aggregate is the item sum over the paths. -/
theorem snd_pathMoment (R : List (X × Y)) (S : List (Y × Z)) (T : List (Z × W)) (u : X × Y → K)
    (v : Y × Z → K) (w : Z × W → K) :
    (pathMoment R S T u v w).snd = ((pathJoin R S T).map fun q =>
      u (q.1, q.2.1) + v (q.2.1, q.2.2.1) + w (q.2.2.1, q.2.2.2)).sum := by
  simp [pathMoment_eq]

end Moments

section MomentFold

variable [DecidableEq Y] [CommSemiring K]

/-- **The translation fold over the join, read from one aggregate.** In any order of the item
values of the answers, `acc ↦ acc + (c * item + d)` returns `init + c * sum + d * count`, and
both come from `joinMoment`. -/
theorem foldall_translation_join (R : List (X × Y)) (S : List (Y × Z)) (u : X × Y → K)
    (w : Y × Z → K) {items : List K}
    (hp : items.Perm ((join R S).map fun t => u (t.1, t.2.1) + w (t.2.1, t.2.2)))
    (c d init : K) :
    foldall (fun item acc => acc + (c * item + d)) items init =
      init + c * (joinMoment R S u w).snd + d * (joinMoment R S u w).fst := by
  rw [SymmetricAffineFold.foldall_add_mul_add, Multiset.coe_eq_coe.2 hp, Multiset.sum_coe,
    Multiset.coe_card, List.length_map, snd_joinMoment, fst_joinMoment]

/-- **The translation fold over the path join, read from one aggregate.** -/
theorem foldall_translation_pathJoin [DecidableEq Z] (R : List (X × Y)) (S : List (Y × Z))
    (T : List (Z × W)) (u : X × Y → K) (v : Y × Z → K) (w : Z × W → K) {items : List K}
    (hp : items.Perm ((pathJoin R S T).map fun q =>
      u (q.1, q.2.1) + v (q.2.1, q.2.2.1) + w (q.2.2.1, q.2.2.2)))
    (c d init : K) :
    foldall (fun item acc => acc + (c * item + d)) items init =
      init + c * (pathMoment R S T u v w).snd + d * (pathMoment R S T u v w).fst := by
  rw [SymmetricAffineFold.foldall_add_mul_add, Multiset.coe_eq_coe.2 hp, Multiset.sum_coe,
    Multiset.coe_card, List.length_map, snd_pathMoment, fst_pathMoment]

end MomentFold

open Mettapedia.GSLT.AffineExpression in
/-- The join fold for the recognized body `acc + (c * item + d)`, over the answer rows in any
order. -/
theorem sourceFold_addMulAdd_join [DecidableEq Y] (R : List (X × Y)) (S : List (Y × Z))
    (u : X × Y → ℤ) (w : Y × Z → ℤ) {rows : List (Fin 1 → ℤ)}
    (hp : rows.Perm ((join R S).map fun t => ![u (t.1, t.2.1) + w (t.2.1, t.2.2)]))
    (c d init : ℤ) :
    sourceFold (SymmetricAffineFold.addMulAdd c d) rows init =
      init + c * (joinMoment R S u w).snd + d * (joinMoment R S u w).fst := by
  rw [SymmetricAffineFold.sourceFold_addMulAdd, Multiset.coe_eq_coe.2 hp, Multiset.map_coe,
    List.map_map, Multiset.sum_coe, Multiset.coe_card, List.length_map, snd_joinMoment,
    fst_joinMoment]
  rfl

/-! ## Enumeration order -/

section Order

variable [DecidableEq Y]

/-- Commutative aggregates do not see the enumeration order. -/
theorem sum_map_join_eq_joinRightMajor {M : Type*} [AddCommMonoid M] (R : List (X × Y))
    (S : List (Y × Z)) (w : X × Y × Z → M) :
    ((join R S).map w).sum = ((joinRightMajor R S).map w).sum :=
  ((join_perm_joinRightMajor R S).map w).sum_eq

/-- Folds whose steps have pairwise commuting coefficients do not see the enumeration order. -/
theorem foldall_join_eq_joinRightMajor {Item Acc M : Type*} [Monoid M] [MulAction Mᵐᵒᵖ Acc]
    {op : Item → Acc → Acc} {coeff : Item → M} (hop : Represents op coeff)
    (R : List (X × Y)) (S : List (Y × Z)) (v : X × Y × Z → Item)
    (hc : ∀ i ∈ (join R S).map v, ∀ j ∈ (join R S).map v, Commute (coeff i) (coeff j))
    (init : Acc) :
    foldall op ((join R S).map v) init = foldall op ((joinRightMajor R S).map v) init :=
  foldall_perm hop ((join_perm_joinRightMajor R S).map v) hc init

/-- Translation folds do not see the enumeration order. -/
theorem foldall_join_eq_joinRightMajor_of_translations {Item : Type*} [Semiring K]
    {op : Item → K → K} {coeff : Item → AffineSummary K} (hop : AffineStep op coeff)
    (htr : ∀ i, (coeff i).scale = 1) (R : List (X × Y)) (S : List (Y × Z))
    (v : X × Y × Z → Item) (init : K) :
    foldall op ((join R S).map v) init = foldall op ((joinRightMajor R S).map v) init :=
  foldall_perm_of_translations hop htr ((join_perm_joinRightMajor R S).map v) init

end Order

/-! ## Controls -/

section Controls

open Mettapedia.GSLT.AffineExpression

/-- Two rows of the left relation meet two rows of the right relation at one key. -/
def orderLeft : List (ℤ × ℤ) := [(1, 0), (2, 0)]

/-- The right relation of the order controls. -/
def orderRight : List (ℤ × ℤ) := [(0, 10), (0, 20)]

/-- The two enumerations list the same answers in different orders. -/
theorem join_order_control :
    join orderLeft orderRight = [(1, 0, 10), (1, 0, 20), (2, 0, 10), (2, 0, 20)] ∧
      joinRightMajor orderLeft orderRight = [(1, 0, 10), (2, 0, 10), (1, 0, 20), (2, 0, 20)] := by
  decide

/-- **Negative control.** The admitted body `2 * acc + item` over the `x` column sees the
enumeration order: `R`-major gives `18`, `S`-major gives `20`. -/
theorem twoAccPlusItem_sees_join_order :
    sourceFold twoAccPlusItem ((join orderLeft orderRight).map fun t => ![t.1]) 0 = 18 ∧
      sourceFold twoAccPlusItem ((joinRightMajor orderLeft orderRight).map fun t => ![t.1]) 0 =
        20 := by
  decide

/-- The translation body `acc + (3 * item + 1)` gives `22` in both orders. -/
theorem addMulAdd_ignores_join_order :
    sourceFold (SymmetricAffineFold.addMulAdd 3 1)
        ((join orderLeft orderRight).map fun t => ![t.1]) 0 = 22 ∧
      sourceFold (SymmetricAffineFold.addMulAdd 3 1)
        ((joinRightMajor orderLeft orderRight).map fun t => ![t.1]) 0 = 22 := by
  decide

/-- A directed graph on `0, 1, 2, 3` whose edge `0 → 1` is stored twice. -/
def edges : List (ℕ × ℕ) := [(0, 1), (0, 1), (1, 2), (1, 3), (2, 0), (2, 3)]

/-- Eight 2-paths, enumerated and by elimination. -/
theorem two_paths_control :
    (join edges edges).length = 8 ∧
      ∑ y ∈ (edges.map Prod.snd).toFinset,
        (edges.countP fun e => e.2 = y) * (edges.countP fun e => e.1 = y) = 8 := by
  decide

/-- Ten 3-paths: enumerated, streamed over the last relation, and summed over the keys. -/
theorem three_paths_control :
    (pathJoin edges edges edges).length = 10 ∧
      (edges.map fun t =>
        groupSum Prod.snd (fun s => edges.countP fun r => r.2 = s.1) edges t.1).sum = 10 ∧
      ∑ z ∈ (edges.map Prod.fst).toFinset,
        message (fun y => edges.countP fun r => r.2 = y) (fun _ => 1) edges z *
          edges.countP (fun t => t.1 = z) = 10 := by
  decide

/-- The source-vertex sum over the 2-paths, enumerated and by elimination. -/
theorem two_path_source_sum_control :
    ((join edges edges).map fun t => t.1).sum = 6 ∧
      ∑ y ∈ (edges.map Prod.snd).toFinset,
        groupSum Prod.snd Prod.fst edges y * (edges.countP fun e => e.1 = y) = 6 := by
  decide

/-- One dual-number aggregate carries both the count `8` and the source-vertex sum `6` of the
2-paths. -/
theorem two_path_moment_control :
    (joinMoment edges edges (fun e => (e.1 : ℤ)) 0).fst = 8 ∧
      (joinMoment edges edges (fun e => (e.1 : ℤ)) 0).snd = 6 := by
  decide

/-- Columns carried by both atoms: over the 2-paths `(x, y, z)`, the sum of `x + z` is `21`,
enumerated and read from the aggregate. -/
theorem two_path_endpoint_sum_control :
    ((join edges edges).map fun t => (t.1 + t.2.2 : ℤ)).sum = 21 ∧
      (joinMoment edges edges (fun e => (e.1 : ℤ)) fun e => (e.2 : ℤ)).snd = 21 := by
  decide

/-- Over the 3-paths `(a, b, c, d)`: `10` paths with `a + d` summing to `28`, enumerated and
read from the path aggregate. -/
theorem three_path_moment_control :
    ((pathJoin edges edges edges).map fun q => (q.1 + q.2.2.2 : ℤ)).sum = 28 ∧
      (pathMoment edges edges edges (fun e => (e.1 : ℤ)) 0 fun e => (e.2 : ℤ)).fst = 10 ∧
      (pathMoment edges edges edges (fun e => (e.1 : ℤ)) 0 fun e => (e.2 : ℤ)).snd = 28 := by
  decide

/-- `acc ↦ acc + (3 * item + 1)` from `10` over the source vertices of the 2-paths gives `36`,
enumerated and read from the aggregate. -/
theorem two_path_fold_control :
    foldall (fun item acc => acc + (3 * item + 1))
        ((join edges edges).map fun t => (t.1 : ℤ)) 10 = 36 ∧
      10 + 3 * (joinMoment edges edges (fun e => (e.1 : ℤ)) 0).snd +
        1 * (joinMoment edges edges (fun e => (e.1 : ℤ)) 0).fst = 36 := by
  decide

end Controls

end Mettapedia.GSLT.Dynamics.JoinAggregation
