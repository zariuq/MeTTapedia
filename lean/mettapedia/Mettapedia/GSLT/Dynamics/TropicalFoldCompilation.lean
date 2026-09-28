import Mettapedia.GSLT.LanguageDef.TropicalExpression
import Mettapedia.GSLT.Dynamics.SymmetricAffineFold

/-!
# Tropical fold compilation: PeTTa `foldall` over min-plus and max-plus steps

PeTTa evaluates `(foldall op generator init)` by applying `(op item acc)` to the generator's
answers in authored order, the first answer first (`AffineFoldCompilation.foldall`). This module
covers step bodies built from integer literals, the answer row, the accumulator, `+`, `-`, `min`
and `max` (PeTTa's binary integer builtins), as recognized by `TropicalExpression.compile e`. The
admitted extremum `e` is `min` or `max`. An accepted body denotes a constant step
`acc ↦ c(row)` or a shift-cap step `acc ↦ e (acc + a(row)) b(row)`, where a missing cap `b` means
`acc ↦ acc + a(row)`. Its row summaries are affine summaries over the min-plus semiring
`Tropical (WithTop ℤ)`; for `max` the accumulator enters negated. The fold is therefore a list
homomorphism into that monoid.

## What is proved

* `toTropical_sourceFold`, `sourceTrajectory_eq`: the source fold and every prefix accumulator,
  carried to the min-plus semiring, are those of the compiled min-plus step (`tropicalStep`),
  whose coefficients are the row summaries. Every law of `AffineFoldCompilation` for represented
  folds, the blocked scan included, therefore applies. `TropicalExpression.summary_correct` is
  the ordered product form, `sourceFold_leaves` gives every bracketing, and `sourceFold_matrix`
  the homogeneous `2 × 2` tropical matrices, last row leftmost.
* `sourceFold_replicate`, **runs by powers**: `k + 1` copies of one row of a compiled shift-cap
  body act as one shift-cap step, with shift `(k + 1) * a` and cap `b + e 0 (k * a)`. The
  algebraic form is `AffineSummary.minPlus_pow_succ`, and `ActionFold.npowBinRec_eq_pow`
  licenses computing the power by repeated squaring.
* `reorder_sound`: rows may be permuted when `reorderable` holds, that is when the compiled form
  is a cap (shift syntactically `0`) or a pure shift (no cap). Caps commute and shifts commute
  (`reorderable_commute`).
* **Idempotent consumers.** If the coefficients of a represented fold commute pairwise and are
  idempotent, the fold over a list equals the fold over its deduplication (`foldall_dedup`) and
  depends only on the set of items (`foldall_eq_of_toFinset_eq`). The summaries of a cap body are
  such coefficients (`isCap_summary`), so its fold depends only on the set of rows
  (`sourceFold_eq_of_toFinset_eq`, `sourceFold_dedup`). In closed form it is the least of the
  initial accumulator and of the caps over that set for `min` (`sourceFold_cap_min`, in
  `WithTop ℤ`), and the greatest for `max` (`sourceFold_cap_max`, in `WithBot ℤ`).
* `sourceFold_shift`: a pure shift body adds the sum of its shifts. Order is unobservable, but
  multiplicity is observable.

## Controls

* Admitted: the running minimum and maximum, the relaxation `min acc (item + 3)`, and
  `min (acc + 1) (acc + 2)`, which is compiled as the pure shift `acc + min 1 2`.
* Refused, and correctly so. `max acc item` is refused by the `min` compiler, and no min-plus
  form denotes it. `acc + acc` and `5 - acc` are refused by both compilers, and no form of either
  extremum denotes them (`not_minPlus_runningMax`, `not_tropical_accPlusAcc`,
  `not_tropical_fiveMinusAcc`).
* Refused although tropical: `min acc (max acc 3)` denotes `acc`
  (`capOfFloor_rejected_but_identity`). The grammar is conservative, and rejection means source
  execution.
* Order matters without a license: `min (acc + item) 5` folds the items `1, -2` from `10` to `3`
  in one order and `5` in the other.
* Multiplicity matters without idempotence: the pure shift `acc + item` counts duplicates.
* Runs: `min (acc - 2) 7` and `max (acc + 2) 1` in closed form for every run length
  (`minusTwoCapSeven_run`, `plusTwoFloorOne_run`).

## What is not covered

* **The unreached state.** Accumulators are integers, so `⊤` in `WithTop ℤ` is never a state; it
  appears only as a missing cap and as the scale of a constant step. A source that uses an
  infinite sentinel needs its own encoding.
* **Numeric representation.** All laws are exact in `ℤ`. `min` and `max` cannot overflow, but
  `+` and `-` can, and a run multiplies the shift by its length. The native realization needs
  an overflow guard for intermediate values as well as for the result.
* **Mixed extrema.** A body using both `min` and `max` on accumulator-dependent terms is refused
  by both compilers. `min acc (max acc 3)` shows the refusal can be conservative. Nested
  alternations such as clamps are not tropical affine in general and have no route here.
* **Effects, errors, fuel, observation.** The source language is pure. The reordering and
  deduplication licenses preserve only the final accumulator, not the trajectory, the first
  answer or any partial observation.

## Mapping to CeTTa native folds

Admission is `compile e body = some out` for the decoded body and for `e = min` or `e = max`.
The compiled artifact is `out`: a constant, or a shift and an optional cap, each an
accumulator-free coefficient expression.

* **Ordered scan.** Evaluate the coefficients per answer and apply `Form.apply`, in answer order
  (`compiledFold_correct`). The min-plus summaries may also be combined in answer order by any
  reduction tree (`sourceFold_leaves`) or prefix scan (`sourceTrajectory_eq`).
* **Runs by powers.** For a run of `k + 1` equal rows, apply one shift-cap step with shift
  `(k + 1) * a` and cap `b + e 0 (k * a)` (`sourceFold_replicate`).
* **Set consumers.** When `isCap out = true`, a consumer that holds only the set of answers, or
  deduplicates them, computes the same fold (`sourceFold_eq_of_toFinset_eq`). An index that
  maintains the least cap over the answers for `min` (the greatest for `max`) gives the fold as
  that value combined with the initial accumulator (`sourceFold_cap_min`,
  `sourceFold_cap_max`).
* When `reorderable out = true` but the form is a pure shift, answers may be reordered but not
  deduplicated.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.TropicalFoldCompilation

open scoped RightActions
open Tropical Mettapedia.Algebra Mettapedia.GSLT.TropicalExpression
open Mettapedia.GSLT.Dynamics.AffineFoldCompilation (foldall foldall_nil foldall_cons trajectory
  Represents foldall_eq foldall_leaves foldall_perm trajectory_eq AffineStep foldall_affine_matrix)

/-! ## Transport along an intertwining map -/

section Transport

variable {Item A B : Type*}

/-- A map intertwining two steps carries the fold of one to the fold of the other. -/
theorem map_foldall (φ : A → B) {op : Item → A → A} {op' : Item → B → B}
    (h : ∀ item x, φ (op item x) = op' item (φ x)) (items : List Item) (init : A) :
    φ (foldall op items init) = foldall op' items (φ init) :=
  (List.foldl_hom φ fun x item => (h item x).symm).symm

/-- A map intertwining two steps carries every prefix accumulator of one fold to the
corresponding prefix accumulator of the other. -/
theorem map_trajectory (φ : A → B) {op : Item → A → A} {op' : Item → B → B}
    (h : ∀ item x, φ (op item x) = op' item (φ x)) (items : List Item) (init : A) :
    (trajectory op items init).map φ = trajectory op' items (φ init) := by
  induction items generalizing init with
  | nil => rfl
  | cons item items ih =>
      simp only [trajectory, List.scanl_cons, List.map_cons] at ih ⊢
      rw [ih, h]

end Transport

/-! ## Idempotent commuting coefficients -/

section Idempotent

variable {Item : Type*} [DecidableEq Item] {M : Type*} [Monoid M]

/-- The ordered product of pairwise commuting idempotent factors is the product over the
deduplicated list. -/
theorem prod_map_dedup (coeff : Item → M) {items : List Item}
    (hc : ∀ i ∈ items, ∀ j ∈ items, Commute (coeff i) (coeff j))
    (hi : ∀ i ∈ items, IsIdempotentElem (coeff i)) :
    (items.dedup.map coeff).prod = (items.map coeff).prod := by
  induction items with
  | nil => rfl
  | cons x items ih =>
      have hc' : ∀ i ∈ items, ∀ j ∈ items, Commute (coeff i) (coeff j) :=
        fun i hi' j hj => hc i (List.mem_cons_of_mem x hi') j (List.mem_cons_of_mem x hj)
      have hi' : ∀ i ∈ items, IsIdempotentElem (coeff i) :=
        fun i h => hi i (List.mem_cons_of_mem x h)
      by_cases hx : x ∈ items
      · have hperm : (items.map coeff).Perm ((x :: items.erase x).map coeff) :=
          (List.perm_cons_erase hx).map coeff
        have hpair : (items.map coeff).Pairwise Commute :=
          List.pairwise_map.mpr (List.pairwise_of_forall_mem_list hc')
        rw [List.dedup_cons_of_mem hx, ih hc' hi', List.map_cons, List.prod_cons,
          hperm.prod_eq' hpair, List.map_cons, List.prod_cons, ← mul_assoc,
          (hi x List.mem_cons_self).eq]
      · rw [List.dedup_cons_of_notMem hx, List.map_cons, List.prod_cons, ih hc' hi',
          List.map_cons, List.prod_cons]

variable {Acc : Type*} [MulAction Mᵐᵒᵖ Acc] {op : Item → Acc → Acc} {coeff : Item → M}

/-- **Deduplication license.** If the coefficients of the items commute pairwise and are
idempotent, the fold over a list equals the fold over its deduplication. -/
theorem foldall_dedup (h : Represents op coeff) {items : List Item}
    (hc : ∀ i ∈ items, ∀ j ∈ items, Commute (coeff i) (coeff j))
    (hi : ∀ i ∈ items, IsIdempotentElem (coeff i)) (init : Acc) :
    foldall op items.dedup init = foldall op items init := by
  rw [foldall_eq h, foldall_eq h, prod_map_dedup coeff hc hi]

/-- **Set consumers.** If the coefficients commute pairwise and are idempotent, the fold depends
only on the set of items: neither their order nor their multiplicity is observable. -/
theorem foldall_eq_of_toFinset_eq (h : Represents op coeff) {items₁ items₂ : List Item}
    (hs : items₁.toFinset = items₂.toFinset)
    (hc : ∀ i ∈ items₁, ∀ j ∈ items₁, Commute (coeff i) (coeff j))
    (hi : ∀ i ∈ items₁, IsIdempotentElem (coeff i)) (init : Acc) :
    foldall op items₁ init = foldall op items₂ init := by
  have hmem : ∀ i, i ∈ items₂ → i ∈ items₁ := fun i hi₂ => by
    rw [← List.mem_toFinset, hs, List.mem_toFinset]
    exact hi₂
  rw [← foldall_dedup h hc hi,
    ← foldall_dedup h (fun i hi₂ j hj₂ => hc i (hmem i hi₂) j (hmem j hj₂))
      (fun i hi₂ => hi i (hmem i hi₂))]
  exact foldall_perm h (List.toFinset_eq_iff_perm_dedup.mp hs)
    (fun i hi' j hj' => hc i (List.mem_dedup.mp hi') j (List.mem_dedup.mp hj')) init

end Idempotent

/-! ## Semilattice folds -/

section Semilattice

variable {Item : Type*} [DecidableEq Item] {α : Type*}

/-- A fold of meets is the meet of the initial value with the meet over the set of items. -/
theorem foldall_inf [SemilatticeInf α] [OrderTop α] (f : Item → α) (items : List Item)
    (init : α) :
    foldall (fun item acc => acc ⊓ f item) items init = init ⊓ items.toFinset.inf f := by
  induction items generalizing init with
  | nil => simp
  | cons item items ih =>
      rw [foldall_cons, ih, List.toFinset_cons, Finset.inf_insert, inf_assoc]

/-- A fold of joins is the join of the initial value with the join over the set of items. -/
theorem foldall_sup [SemilatticeSup α] [OrderBot α] (f : Item → α) (items : List Item)
    (init : α) :
    foldall (fun item acc => acc ⊔ f item) items init = init ⊔ items.toFinset.sup f :=
  foldall_inf (α := αᵒᵈ) f items init

end Semilattice

/-! ## Compiled bodies -/

section Compiled

variable {n : ℕ}

/-- The source step of a fold body: evaluate the body with the answer row as its inputs and the
accumulator as `acc`. -/
def sourceStep (body : Expr n) : (Fin n → ℤ) → ℤ → ℤ := fun row acc => body.eval row acc

theorem sourceFold_eq_foldall (body : Expr n) (rows : List (Fin n → ℤ)) (init : ℤ) :
    sourceFold body rows init = foldall (sourceStep body) rows init :=
  rfl

/-- The min-plus step of a compiled form: act by the summary of the row. -/
def tropicalStep (e : Extremum) (out : Form n) (row : Fin n → ℤ) (x : Tropical (WithTop ℤ)) :
    Tropical (WithTop ℤ) :=
  (out.summary e row).act x

theorem tropicalStep_affine (e : Extremum) (out : Form n) :
    AffineStep (tropicalStep e out) (out.summary e) :=
  fun _ _ => rfl

/-- Carried to the min-plus semiring, the source step of an accepted body is its min-plus
step. -/
theorem toTropical_sourceStep {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (row : Fin n → ℤ) (acc : ℤ) :
    e.toTropical (sourceStep body row acc) = tropicalStep e out row (e.toTropical acc) := by
  rw [sourceStep, ← compile_sound e body out h, ← Form.act_summary]
  rfl

/-- An accepted body's source fold, carried to the min-plus semiring, is the fold of its
min-plus step. -/
theorem toTropical_sourceFold {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (rows : List (Fin n → ℤ)) (init : ℤ) :
    e.toTropical (sourceFold body rows init) =
      foldall (tropicalStep e out) rows (e.toTropical init) :=
  map_foldall e.toTropical (toTropical_sourceStep h) rows init

/-- **Scan exactness.** Carried to the min-plus semiring, every prefix accumulator of an
accepted body's source fold is the initial state acted on by one prefix product of the row
summaries. A parallel prefix scan of the summaries computes the whole trajectory. -/
theorem sourceTrajectory_eq {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (rows : List (Fin n → ℤ)) (init : ℤ) :
    (trajectory (sourceStep body) rows init).map e.toTropical =
      ((rows.map (out.summary e)).scanl (· * ·) 1).map (·.act (e.toTropical init)) := by
  rw [map_trajectory e.toTropical (toTropical_sourceStep h) rows init]
  exact trajectory_eq (tropicalStep_affine e out).represents rows _

/-- **Bracketing independence.** Every bracketing of the rows computes the source fold. -/
theorem sourceFold_leaves {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (t : FreeMagma (Fin n → ℤ)) (init : ℤ) :
    e.toTropical (sourceFold body (ActionFold.leaves t) init) =
      (FreeMagma.lift (out.summary e) t).act (e.toTropical init) := by
  rw [toTropical_sourceFold h]
  exact foldall_leaves (tropicalStep_affine e out).represents t _

/-- **Homogeneous tropical matrices.** The column `(state, 1)` after the fold is the product of
the row matrices, last row leftmost, applied to the column `(initial state, 1)`. -/
theorem sourceFold_matrix {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (rows : List (Fin n → ℤ)) (init : ℤ) :
    ![e.toTropical (sourceFold body rows init), 1] =
      ((rows.map (out.summary e)).map AffineSummary.matrix).reverse.prod.mulVec
        ![e.toTropical init, 1] := by
  rw [toTropical_sourceFold h]
  exact foldall_affine_matrix (tropicalStep_affine e out) rows _

/-! ### Runs by powers -/

/-- The summary of a run of `k + 1` equal shift-cap steps, in integer terms: shift
`(k + 1) * a`, cap `b + e 0 (k * a)`. -/
theorem shiftCapSummary_pow_succ (e : Extremum) (a : ℤ) (b : Option ℤ) (k : ℕ) :
    e.shiftCapSummary a b ^ (k + 1) =
      e.shiftCapSummary (((k : ℤ) + 1) * a) (b.map fun c => c + e.eval 0 ((k : ℤ) * a)) := by
  have hmul : ∀ m : ℕ, e.toMin ((m : ℤ) * a) = m • e.toMin a := fun m => by
    rw [← nsmul_eq_mul, map_nsmul]
  simp only [Extremum.shiftCapSummary, AffineSummary.minPlus_pow_succ]
  congr 1
  · rw [← Nat.cast_add_one, hmul]
  · cases b with
    | none => exact WithTop.top_add _
    | some c =>
        simp only [Option.elim, Option.map_some, map_add, Extremum.toMin_eval, map_zero, hmul,
          WithTop.coe_add]

/-- **Runs by powers.** `k + 1` copies of one row of a compiled shift-cap body act as a single
shift-cap step, with shift `(k + 1) * a` and cap `b + e 0 (k * a)`. -/
theorem sourceFold_replicate {e : Extremum} {body : Expr n} {a : Coeff n}
    {b : Option (Coeff n)} (h : compile e body = some (.shift a b)) (k : ℕ) (row : Fin n → ℤ)
    (init : ℤ) :
    sourceFold body (List.replicate (k + 1) row) init =
      e.shiftCap (((k : ℤ) + 1) * a.eval row)
        (b.map fun c => c.eval row + e.eval 0 ((k : ℤ) * a.eval row)) init := by
  apply e.toTropical_injective
  rw [← summary_correct e body _ h, List.map_replicate, List.prod_replicate, Form.summary,
    shiftCapSummary_pow_succ, Extremum.act_shiftCapSummary, Option.map_map]
  rfl

/-! ### Reordering and set consumers -/

/-- Set-consumer admission: the compiled form is a cap `acc ↦ e acc b`, its shift syntactically
the constant `0`. -/
def isCap : Form n → Bool
  | .const _ => false
  | .shift a _ => a.const? == some 0

/-- Reordering admission: a cap, or a pure shift `acc ↦ acc + a` with no cap. -/
def reorderable : Form n → Bool
  | .const _ => false
  | .shift _ none => true
  | .shift a (some _) => a.const? == some 0

/-- The summaries of a cap form are min-plus caps. -/
theorem isCap_summary {e : Extremum} {out : Form n} (hc : isCap out = true) (row : Fin n → ℤ) :
    ∃ b : WithTop ℤ, out.summary e row = AffineSummary.minPlus 0 b := by
  rcases out with c | ⟨a, b⟩
  · simp [isCap] at hc
  · simp only [isCap, beq_iff_eq] at hc
    exact ⟨_, by rw [Form.summary, Extremum.shiftCapSummary, Coeff.const?_sound hc, map_zero]⟩

theorem reorderable_commute {e : Extremum} {out : Form n} (hr : reorderable out = true)
    (row row' : Fin n → ℤ) : Commute (out.summary e row) (out.summary e row') := by
  rcases out with c | ⟨a, _ | b⟩
  · simp [reorderable] at hr
  · exact AffineSummary.commute_minPlus_top _ _
  · simp only [reorderable, beq_iff_eq] at hr
    simp only [Form.summary, Extremum.shiftCapSummary, Coeff.const?_sound hr, map_zero]
    exact AffineSummary.commute_minPlus_zero _ _

/-- **Reordering admission is sound.** -/
theorem reorder_sound {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (hr : reorderable out = true)
    {rows₁ rows₂ : List (Fin n → ℤ)} (hp : rows₁.Perm rows₂) (init : ℤ) :
    sourceFold body rows₁ init = sourceFold body rows₂ init := by
  apply e.toTropical_injective
  rw [toTropical_sourceFold h, toTropical_sourceFold h]
  exact foldall_perm (tropicalStep_affine e out).represents hp
    (fun row _ row' _ => reorderable_commute hr row row') _

/-- **Set-consumer admission is sound.** A compiled cap body folds to the same value on any two
row lists with the same set of rows. -/
theorem sourceFold_eq_of_toFinset_eq {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (hc : isCap out = true) {rows₁ rows₂ : List (Fin n → ℤ)}
    (hs : rows₁.toFinset = rows₂.toFinset) (init : ℤ) :
    sourceFold body rows₁ init = sourceFold body rows₂ init := by
  apply e.toTropical_injective
  rw [toTropical_sourceFold h, toTropical_sourceFold h]
  refine foldall_eq_of_toFinset_eq (tropicalStep_affine e out).represents hs
    (fun row _ row' _ => ?_) (fun row _ => ?_) _
  · obtain ⟨b, hb⟩ := isCap_summary (e := e) hc row
    obtain ⟨b', hb'⟩ := isCap_summary (e := e) hc row'
    rw [hb, hb']
    exact AffineSummary.commute_minPlus_zero b b'
  · obtain ⟨b, hb⟩ := isCap_summary (e := e) hc row
    rw [hb]
    exact AffineSummary.isIdempotentElem_minPlus_zero b

/-- A compiled cap body may deduplicate its rows. -/
theorem sourceFold_dedup {e : Extremum} {body : Expr n} {out : Form n}
    (h : compile e body = some out) (hc : isCap out = true) (rows : List (Fin n → ℤ))
    (init : ℤ) : sourceFold body rows.dedup init = sourceFold body rows init :=
  sourceFold_eq_of_toFinset_eq h hc
    (List.toFinset_eq_iff_perm_dedup.mpr (by rw [List.dedup_idem])) init

/-- **Cap folds for `min`.** A compiled `min` cap body folds to the least of the initial
accumulator and of the caps over the set of rows; a missing cap is `⊤`. -/
theorem sourceFold_cap_min {body : Expr n} {a : Coeff n} {b : Option (Coeff n)}
    (h : compile .min body = some (.shift a b)) (ha : a.const? = some 0)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    (sourceFold body rows init : WithTop ℤ) =
      min (init : WithTop ℤ)
        (rows.toFinset.inf fun row => b.elim ⊤ fun c => (c.eval row : WithTop ℤ)) := by
  rw [sourceFold_eq_foldall, map_foldall (fun x : ℤ => (x : WithTop ℤ))
    (op' := fun row x => x ⊓ b.elim ⊤ fun c => (c.eval row : WithTop ℤ)) ?_ rows init]
  · exact foldall_inf _ rows _
  · intro row acc
    rw [sourceStep, ← compile_sound .min body _ h, Form.apply, Coeff.const?_sound ha]
    cases b <;> simp [Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval]

/-- **Cap folds for `max`.** A compiled `max` cap body folds to the greatest of the initial
accumulator and of the caps over the set of rows; a missing cap is `⊥`. -/
theorem sourceFold_cap_max {body : Expr n} {a : Coeff n} {b : Option (Coeff n)}
    (h : compile .max body = some (.shift a b)) (ha : a.const? = some 0)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    (sourceFold body rows init : WithBot ℤ) =
      max (init : WithBot ℤ)
        (rows.toFinset.sup fun row => b.elim ⊥ fun c => (c.eval row : WithBot ℤ)) := by
  rw [sourceFold_eq_foldall, map_foldall (fun x : ℤ => (x : WithBot ℤ))
    (op' := fun row x => x ⊔ b.elim ⊥ fun c => (c.eval row : WithBot ℤ)) ?_ rows init]
  · exact foldall_sup _ rows _
  · intro row acc
    rw [sourceStep, ← compile_sound .max body _ h, Form.apply, Coeff.const?_sound ha]
    cases b <;> simp [Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval]

/-- **Shift folds.** A compiled pure shift `acc ↦ acc + a` folds to the initial accumulator plus
the sum of the shifts, counted with multiplicity. -/
theorem sourceFold_shift {e : Extremum} {body : Expr n} {a : Coeff n}
    (h : compile e body = some (.shift a none)) (rows : List (Fin n → ℤ)) (init : ℤ) :
    sourceFold body rows init = init + (rows.map a.eval).sum := by
  rw [sourceFold_eq_foldall]
  exact SymmetricAffineFold.foldall_eq_add_sum
    (coeff := fun row => AffineSummary.translation (a.eval row))
    (fun row acc => by
      rw [AffineSummary.act_translation, sourceStep, ← compile_sound e body _ h]
      rfl)
    (fun _ => rfl) rows init

end Compiled

/-! ## Controls -/

section Controls

/-- `min acc item`: the running minimum. -/
def runningMin : Expr 1 := .bin .min .acc (.input 0)

/-- `max acc item`: the running maximum. -/
def runningMax : Expr 1 := .bin .max .acc (.input 0)

/-- `min acc (item + 3)`: relax a distance by a candidate `item` over an edge of weight `3`. -/
def relaxThree : Expr 1 := .bin .min .acc (.bin .add (.input 0) (.lit 3))

/-- `min (acc + 1) (acc + 2)`. -/
def minOfShifts : Expr 1 := .bin .min (.bin .add .acc (.lit 1)) (.bin .add .acc (.lit 2))

/-- `min (acc + item) 5`. -/
def shiftItemCapFive : Expr 1 := .bin .min (.bin .add .acc (.input 0)) (.lit 5)

/-- `min (acc - 2) 7`. -/
def minusTwoCapSeven : Expr 1 := .bin .min (.bin .sub .acc (.lit 2)) (.lit 7)

/-- `max (acc + 2) 1`. -/
def plusTwoFloorOne : Expr 1 := .bin .max (.bin .add .acc (.lit 2)) (.lit 1)

/-- `acc + item`. -/
def accPlusItem : Expr 1 := .bin .add .acc (.input 0)

/-- `min acc (max acc 3)`, which denotes `acc`. -/
def capOfFloor : Expr 1 := .bin .min .acc (.bin .max .acc (.lit 3))

/-- `acc + acc`. -/
def accPlusAcc : Expr 1 := .bin .add .acc .acc

/-- `5 - acc`. -/
def fiveMinusAcc : Expr 1 := .bin .sub (.lit 5) .acc

/-- The running minimum is a `min` cap and is refused by the `max` compiler; the running maximum
is the mirror image. -/
theorem running_extrema_admission :
    (compile .min runningMin).map isCap = some true ∧ compile .max runningMin = none ∧
      (compile .max runningMax).map isCap = some true ∧ compile .min runningMax = none := by
  decide

/-- The running minimum of `5, 3, 8, 3` from `100` is `3`, as is that of `8, 3, 5`, which has the
same set of items. The running maximum of `5, 3, 8, 3` from `-100` is `8`. -/
theorem running_extrema_control :
    sourceFold runningMin [![5], ![3], ![8], ![3]] 100 = 3 ∧
      sourceFold runningMin [![8], ![3], ![5]] 100 = 3 ∧
      sourceFold runningMax [![5], ![3], ![8], ![3]] (-100) = 8 := by
  decide

/-- The running minimum in closed form: the least of the initial accumulator and of the items. -/
theorem runningMin_eq (rows : List (Fin 1 → ℤ)) (init : ℤ) :
    (sourceFold runningMin rows init : WithTop ℤ) =
      min (init : WithTop ℤ) (rows.toFinset.inf fun row => ((row 0 : ℤ) : WithTop ℤ)) := by
  rw [sourceFold_cap_min (a := .lit 0) (b := some (.input 0)) rfl rfl]
  rfl

/-- The running maximum in closed form: the greatest of the initial accumulator and of the
items. -/
theorem runningMax_eq (rows : List (Fin 1 → ℤ)) (init : ℤ) :
    (sourceFold runningMax rows init : WithBot ℤ) =
      max (init : WithBot ℤ) (rows.toFinset.sup fun row => ((row 0 : ℤ) : WithBot ℤ)) := by
  rw [sourceFold_cap_max (a := .lit 0) (b := some (.input 0)) rfl rfl]
  rfl

/-- Relaxation over an edge of weight `3` is a cap. From the tentative distance `100`, the
candidates `10, 4, 7` give `7`. -/
theorem relaxThree_control :
    (compile .min relaxThree).map isCap = some true ∧
      sourceFold relaxThree [![10], ![4], ![7]] 100 = 7 := by
  decide

/-- Relaxation in closed form: the least of the tentative distance and of `item + 3` over the
set of candidates. -/
theorem relaxThree_eq (rows : List (Fin 1 → ℤ)) (init : ℤ) :
    (sourceFold relaxThree rows init : WithTop ℤ) =
      min (init : WithTop ℤ) (rows.toFinset.inf fun row => ((row 0 + 3 : ℤ) : WithTop ℤ)) := by
  rw [sourceFold_cap_min (a := .lit 0) (b := some (.bin .add (.input 0) (.lit 3))) rfl rfl]
  rfl

/-- `min (acc + 1) (acc + 2)` is admitted as the pure shift `acc + min 1 2`: shifts combine by
`min`. It denotes `acc + 1`, and its rows may be reordered. The `max` compiler refuses it. -/
theorem minOfShifts_admitted :
    compile .min minOfShifts =
        some (.shift (.bin .min (.bin .add (.lit 0) (.lit 1)) (.bin .add (.lit 0) (.lit 2))) none) ∧
      (compile .min minOfShifts).map reorderable = some true ∧
      compile .max minOfShifts = none ∧
      ∀ row acc, minOfShifts.eval row acc = acc + 1 := by
  refine ⟨rfl, rfl, rfl, fun row acc => ?_⟩
  simp only [minOfShifts, Expr.eval, Op.eval]
  omega

/-- `max acc item` is refused by the `min` compiler, and correctly so: no min-plus form denotes
it, whatever its coefficients evaluate to. -/
theorem not_minPlus_runningMax :
    ¬ ∃ f : Form 1, ∀ row acc, f.apply .min row acc = runningMax.eval row acc := by
  rintro ⟨f, hf⟩
  have h₁ := hf ![0] (-1)
  have h₂ := hf ![0] 0
  have h₃ := hf ![0] 1
  rcases f with c | ⟨a, _ | b⟩ <;>
    simp [Form.apply, Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval, runningMax,
      Expr.eval] at h₁ h₂ h₃ <;> omega

/-- `acc + acc` has degree `2`, is refused by both compilers, and no form of either extremum
denotes it. -/
theorem not_tropical_accPlusAcc :
    accPlusAcc.degree .min = 2 ∧ compile .min accPlusAcc = none ∧
      compile .max accPlusAcc = none ∧
      ∀ e, ¬ ∃ f : Form 1, ∀ row acc, f.apply e row acc = accPlusAcc.eval row acc := by
  refine ⟨rfl, rfl, rfl, fun e => ?_⟩
  rintro ⟨f, hf⟩
  have h₀ := hf ![0] 0
  have h₁ := hf ![0] 1
  have h₂ := hf ![0] 2
  cases e <;> rcases f with c | ⟨a, _ | b⟩ <;>
    simp [Form.apply, Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval, accPlusAcc,
      Expr.eval] at h₀ h₁ h₂ <;> omega

/-- `5 - acc` is decreasing in the accumulator, is refused by both compilers, and no form of
either extremum denotes it. -/
theorem not_tropical_fiveMinusAcc :
    fiveMinusAcc.degree .min = ⊤ ∧ compile .min fiveMinusAcc = none ∧
      compile .max fiveMinusAcc = none ∧
      ∀ e, ¬ ∃ f : Form 1, ∀ row acc, f.apply e row acc = fiveMinusAcc.eval row acc := by
  refine ⟨rfl, rfl, rfl, fun e => ?_⟩
  rintro ⟨f, hf⟩
  have h₀ := hf ![0] 0
  have h₁ := hf ![0] 1
  cases e <;> rcases f with c | ⟨a, _ | b⟩ <;>
    simp [Form.apply, Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval, fiveMinusAcc,
      Expr.eval] at h₀ h₁ <;> omega

/-- The grammar is conservative: `min acc (max acc 3)` denotes `acc` but is refused by both
compilers, so admission falls back to source execution. -/
theorem capOfFloor_rejected_but_identity :
    compile .min capOfFloor = none ∧ compile .max capOfFloor = none ∧
      ∀ row acc, capOfFloor.eval row acc = acc := by
  refine ⟨rfl, rfl, fun row acc => ?_⟩
  simp only [capOfFloor, Expr.eval, Op.eval]
  omega

/-- `min (acc + item) 5` is admitted but neither a cap nor a pure shift, and its fold depends on
the order of the items: `1, -2` from `10` gives `3`, and `-2, 1` gives `5`. -/
theorem shiftItemCapFive_order_matters :
    (compile .min shiftItemCapFive).map reorderable = some false ∧
      sourceFold shiftItemCapFive [![1], ![-2]] 10 = 3 ∧
      sourceFold shiftItemCapFive [![-2], ![1]] 10 = 5 := by
  decide

/-- A run of `min (acc - 2) 7` in closed form: `k + 1` steps from `init` give
`min (init - 2 * (k + 1)) (7 - 2 * k)`. The shift is negative, so the cap of the run moves down
with its length. -/
theorem minusTwoCapSeven_run (k : ℕ) (row : Fin 1 → ℤ) (init : ℤ) :
    sourceFold minusTwoCapSeven (List.replicate (k + 1) row) init =
      min (init - 2 * ((k : ℤ) + 1)) (7 - 2 * k) := by
  rw [sourceFold_replicate (e := .min) (a := .bin .sub (.lit 0) (.lit 2)) (b := some (.lit 7)) rfl]
  simp only [Option.map_some, Extremum.shiftCap, Option.elim, Extremum.eval, Extremum.op,
    Op.eval, Coeff.eval]
  omega

/-- Three steps of `min (acc - 2) 7` from `20` give `3 = min 14 3`. -/
theorem minusTwoCapSeven_control :
    sourceFold minusTwoCapSeven (List.replicate 3 ![0]) 20 = 3 := by
  decide

/-- A run of `max (acc + 2) 1` in closed form: `k + 1` steps from `init` give
`max (init + 2 * (k + 1)) (1 + 2 * k)`. Under `max` the cap is a floor, and a positive shift
raises it with the length of the run. -/
theorem plusTwoFloorOne_run (k : ℕ) (row : Fin 1 → ℤ) (init : ℤ) :
    sourceFold plusTwoFloorOne (List.replicate (k + 1) row) init =
      max (init + 2 * ((k : ℤ) + 1)) (1 + 2 * k) := by
  rw [sourceFold_replicate (e := .max) (a := .bin .add (.lit 0) (.lit 2)) (b := some (.lit 1)) rfl]
  simp only [Option.map_some, Extremum.shiftCap, Option.elim, Extremum.eval, Extremum.op,
    Op.eval, Coeff.eval]
  omega

/-- The pure shift `acc + item` may be reordered but not deduplicated: duplicates count. -/
theorem accPlusItem_duplicates_count :
    (compile .min accPlusItem).map reorderable = some true ∧
      (compile .min accPlusItem).map isCap = some false ∧
      sourceFold accPlusItem [![1], ![1]] 0 = 2 ∧ sourceFold accPlusItem [![1]] 0 = 1 := by
  decide

end Controls

end Mettapedia.GSLT.Dynamics.TropicalFoldCompilation
