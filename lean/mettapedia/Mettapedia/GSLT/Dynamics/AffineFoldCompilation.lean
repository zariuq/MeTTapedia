import Mettapedia.Algebra.MatrixAffineSummary
import Mettapedia.GSLT.LanguageDef.AffineExpression
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.ENat.Basic

/-!
# Affine fold compilation: PeTTa `foldall` as a list homomorphism

PeTTa evaluates `(foldall op generator init)` by folding the generator's
answers in authored order, applying each answer as `(op item acc)`. That is
`foldall` below: the first answer is applied first. Fold admission compiles
such a fold when its step acts on the accumulator through a monoid of
coefficients. The canonical case is a body affine in the accumulator,
`acc ↦ a(item) * acc + b(item)`, with coefficients in the monoid
`AffineSummary`. The fold is then a list homomorphism into that monoid. This
module proves what that licenses and what it does not.

## What is proved

For any monoid `M` acting on the accumulator on the right, and any step `op`
represented by `coeff : Item → M` (`Represents op coeff`):

* `foldall_eq`: the fold equals `init <• (items.map coeff).prod`, the action
  of the ordered product with the first item leftmost;
* `foldall_leaves`: every bracketing (a Mathlib `FreeMagma` tree) of the
  ordered items computes the fold, so any reduction tree is exact;
* `trajectory_eq`, `getElem_trajectory`: every prefix accumulator is `init`
  acted on by the prefix product, so a parallel prefix scan in the monoid
  computes the whole trajectory;
* `trajectory_flatten`: the three-phase blocked scan is exact. Its phases are
  chunk products, a scan of those products, and chunk-local scans from each
  chunk's start;
* `foldall_replicate`: a run of one constant item is a power. Closed forms
  are `AffineSummary.pow_eq` and its ring and integer variants; repeated
  squaring is licensed by `ActionFold.npowBinRec_eq_pow`;
* `foldall_perm`: reordering is licensed when the coefficients pairwise
  commute, and `perm_without_commutation_changes_fold` shows that the
  hypothesis cannot be dropped. Translations always commute, and scalings
  commute over a commutative semiring (`foldall_perm_of_translations`,
  `foldall_perm_of_scalings`).

The scalar instance covers PeTTa's integer `+`, `*` and `-` steps
(`add_step`, `mul_step`, `sub_step`). The linear-state instance covers
`x ↦ M(item) *ᵥ x + v(item)` over any semiring. The tropical min-plus
instance is edge relaxation (`relaxation_pass_eq`), with a concrete
shortest-path control.

The checked recognizer is `Mettapedia.GSLT.AffineExpression.compile`, over
exact integer literals, input coordinates, one accumulator, and binary
`+ - *`. `affineStep_of_compile` makes every accepted body an affine step
whose coefficients are the compiled accumulator-free coefficient syntax.
`compile_coeffs_sound` states the contract in coefficient form. All fold
laws above then apply to `sourceFold`. `reorderable` is a decidable,
syntactic reordering admission for compiled bodies, and `reorder_sound`
proves it sound.

## Controls

The fold-level controls are these. Add-one then multiply-by-two differs from
the reverse order. A permutation without commutation changes the fold. PeTTa
subtraction is order-sensitive. A reordered sum keeps its final value but
not its trajectory. A reversed tropical relaxation pass computes a different
distance vector. For the recognizer, four representative bodies are accepted:
`acc + 3 * item`, `-acc + 3 * item` (written `(0 - acc) + 3 * item`, since
PeTTa's `-` is binary), `item * acc + 1` and `2 * acc + item`. The body
`acc * acc + item` is rejected and provably not affine for any coefficients.
The body `(acc + 1) * (acc + 1) - acc * acc` is rejected although it denotes
`2 * acc + 1`. The grammar is conservative, and rejection means falling back
to source execution.

## What is not covered (C-side guards)

* **Numeric representation.** All laws are exact arithmetic in `ℤ` or the
  stated semiring. Machine-integer overflow, bigint promotion and
  floating-point rounding need guards in the native realization. A final
  value that fits proves nothing about intermediate values; see
  `AffineExpression.Controls.final_fit_is_insufficient`.
* **Floor `%` and division.** Neither is affine, and neither has a
  constructor in the recognized syntax. Folds using them stay ordered scans.
* **Errors and effects.** The source language is pure. Operator lookup,
  dialect, type promotion, errors, space mutation and generator effects must
  be resolved before admission.
* **Fuel and cost.** No statement here concerns evaluation cost, fuel or
  interruption. The DSL charge is in `AffineExpressionRealization`.
* **Observation of intermediate states.** `foldall_perm` preserves only the
  final accumulator. A consumer that observes the trajectory, the first
  answer, or a partial fold is outside the reordering license
  (`reordered_sum_trajectory_differs`).
* **The answer stream.** The item list is a fixed, finite, ordered
  occurrence list. Duplicates count, and order matters unless reordering is
  licensed. A generator that reacts to the accumulator needs a stronger
  theorem.

## Mapping to CeTTa fold admission

For a `foldall` whose step body decodes to `AffineExpression.Expr n`, admission
is `compile body = some out`. The compiled artifact is the pair of coefficient
expressions `out.scale` and `out.offset`, which never mention the accumulator.
Execution may then evaluate `out.summary row` per answer and combine in the
monoid: sequentially, as any reduction tree, as a blocked scan, or by
repeated squaring for a constant run. Permuting answers is licensed when
`reorderable out = true`, a sufficient syntactic condition, and only if
intermediate accumulators are not observed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.AffineFoldCompilation

open scoped RightActions
open Mettapedia.Algebra Mettapedia.Algebra.ActionFold

universe uItem uAcc uM

/-! ## PeTTa fold semantics -/

section Semantics

variable {Item : Type uItem} {Acc : Type uAcc}

/-- PeTTa's `(foldall op generator init)` over the generator's ordered
answers: every answer is applied as `(op item acc)`, the first answer
first. -/
def foldall (op : Item → Acc → Acc) (items : List Item) (init : Acc) : Acc :=
  items.foldl (fun acc item => op item acc) init

/-- The accumulator after every prefix of the answers, starting with
`init`. -/
def trajectory (op : Item → Acc → Acc) (items : List Item) (init : Acc) : List Acc :=
  items.scanl (fun acc item => op item acc) init

@[simp] theorem foldall_nil (op : Item → Acc → Acc) (init : Acc) : foldall op [] init = init :=
  rfl

@[simp] theorem foldall_cons (op : Item → Acc → Acc) (item : Item) (items : List Item)
    (init : Acc) : foldall op (item :: items) init = foldall op items (op item init) :=
  rfl

theorem foldall_append (op : Item → Acc → Acc) (xs ys : List Item) (init : Acc) :
    foldall op (xs ++ ys) init = foldall op ys (foldall op xs init) :=
  List.foldl_append

theorem trajectory_append (op : Item → Acc → Acc) (xs ys : List Item) (init : Acc) :
    trajectory op (xs ++ ys) init =
      trajectory op xs init ++ (trajectory op ys (foldall op xs init)).tail :=
  List.scanl_append

/-- The trajectory starts at `init`. -/
theorem trajectory_eq_cons_tail (op : Item → Acc → Acc) (items : List Item) (init : Acc) :
    trajectory op items init = init :: (trajectory op items init).tail := by
  cases items <;> simp [trajectory]

/-- The trajectory ends at the fold. -/
theorem getLast_trajectory (op : Item → Acc → Acc) (items : List Item) (init : Acc)
    (h : trajectory op items init ≠ []) :
    (trajectory op items init).getLast h = foldall op items init :=
  List.getLast_scanl h

end Semantics

/-! ## Representation by a coefficient monoid -/

section Representation

variable {Item : Type uItem} {Acc : Type uAcc} {M : Type uM} [Monoid M] [MulAction Mᵐᵒᵖ Acc]

/-- `coeff` represents the step `op` when applying an item acts on the
accumulator by that item's coefficient. -/
def Represents (op : Item → Acc → Acc) (coeff : Item → M) : Prop :=
  ∀ item acc, op item acc = acc <• coeff item

variable {op : Item → Acc → Acc} {coeff : Item → M}

theorem foldall_eq_foldl (h : Represents op coeff) (items : List Item) (init : Acc) :
    foldall op items init = items.foldl (fun state item => state <• coeff item) init := by
  have h' : ∀ item acc, op item acc = acc <• coeff item := h
  simp only [foldall, h']

/-- **Fold exactness.** A represented fold is the action of the ordered
product of coefficients, first item leftmost. -/
theorem foldall_eq (h : Represents op coeff) (items : List Item) (init : Acc) :
    foldall op items init = init <• (items.map coeff).prod := by
  rw [foldall_eq_foldl h, foldl_map_op_smul]

/-- **Bracketing independence.** Every bracketing of the ordered items
computes the fold. -/
theorem foldall_leaves (h : Represents op coeff) (t : FreeMagma Item) (init : Acc) :
    foldall op (leaves t) init = init <• FreeMagma.lift coeff t := by
  rw [foldall_eq_foldl h, foldl_leaves]

/-- **Scan exactness.** The trajectory is `init` acted on by the prefix
products. A parallel prefix scan in `M` computes it. -/
theorem trajectory_eq (h : Represents op coeff) (items : List Item) (init : Acc) :
    trajectory op items init = ((items.map coeff).scanl (· * ·) 1).map (init <• ·) := by
  have h' : ∀ item acc, op item acc = acc <• coeff item := h
  have hmap : trajectory op items init =
      (items.map coeff).scanl (fun state m => state <• m) init := by
    rw [List.scanl_map]
    simp only [trajectory, h']
  rw [hmap, scanl_op_smul]

/-- Every prefix accumulator is `init` acted on by one prefix product. -/
theorem getElem_trajectory (h : Represents op coeff) (items : List Item) (init : Acc) (i : ℕ)
    (hi : i < (trajectory op items init).length) :
    (trajectory op items init)[i] = init <• ((items.take i).map coeff).prod := by
  simp only [trajectory, List.getElem_scanl]
  exact foldall_eq h (items.take i) init

/-- **Blocked scan.** Phase 1 multiplies each chunk's coefficients. Phase 2
scans those chunk products from `init`, giving every chunk's start. Phase 3
runs every chunk's trajectory from its own start, independently. Dropping
each repeated start and concatenating gives the sequential trajectory. -/
theorem trajectory_flatten (h : Represents op coeff) (chunks : List (List Item))
    (init : Acc) :
    trajectory op chunks.flatten init =
      init :: (List.zipWith (fun start chunk => (trajectory op chunk start).tail)
        ((chunks.map fun chunk => (chunk.map coeff).prod).scanl
          (fun state m => state <• m) init) chunks).flatten := by
  induction chunks generalizing init with
  | nil => simp [trajectory]
  | cons chunk chunks ih =>
      rw [List.flatten_cons, trajectory_append, foldall_eq h, ih, List.tail_cons,
        List.map_cons, List.scanl_cons, List.zipWith_cons_cons, List.flatten_cons,
        ← List.cons_append, ← trajectory_eq_cons_tail]

/-- A run of one constant item acts as a power of its coefficient. -/
theorem foldall_replicate (h : Represents op coeff) (n : ℕ) (item : Item) (init : Acc) :
    foldall op (List.replicate n item) init = init <• coeff item ^ n := by
  rw [foldall_eq h, List.map_replicate, List.prod_replicate]

/-- **Reordering license.** Answers may be permuted when their coefficients
pairwise commute. Only the final accumulator is preserved. -/
theorem foldall_perm (h : Represents op coeff) {items₁ items₂ : List Item}
    (hp : items₁.Perm items₂)
    (hc : ∀ i ∈ items₁, ∀ j ∈ items₁, Commute (coeff i) (coeff j)) (init : Acc) :
    foldall op items₁ init = foldall op items₂ init := by
  rw [foldall_eq_foldl h, foldall_eq_foldl h]
  exact foldl_map_op_smul_perm coeff hp hc init

end Representation

/-! ## Scalar affine steps -/

section Scalar

variable {Item : Type uItem} {R : Type*}

/-- The step is affine in the accumulator: `op item acc = a(item) * acc + b(item)`,
with coefficients `coeff item = ⟨a(item), b(item)⟩` not depending on `acc`. -/
def AffineStep [Semiring R] (op : Item → R → R) (coeff : Item → AffineSummary R) : Prop :=
  ∀ item acc, op item acc = (coeff item).act acc

theorem affineStep_iff_represents [Semiring R] {op : Item → R → R}
    {coeff : Item → AffineSummary R} : AffineStep op coeff ↔ Represents op coeff :=
  Iff.rfl

variable [Semiring R] {op : Item → R → R} {coeff : Item → AffineSummary R}

/-- An affine step is represented by its coefficient summaries. -/
theorem AffineStep.represents (h : AffineStep op coeff) : Represents op coeff := h

/-- **Affine fold exactness.** -/
theorem foldall_affine (h : AffineStep op coeff) (items : List Item) (init : R) :
    foldall op items init = (items.map coeff).prod.act init :=
  foldall_eq h.represents items init

/-- The affine fold in homogeneous coordinates: the column `(init, 1)` times
the item matrices, last item leftmost. -/
theorem foldall_affine_matrix (h : AffineStep op coeff) (items : List Item) (init : R) :
    ![foldall op items init, 1] =
      ((items.map coeff).map AffineSummary.matrix).reverse.prod.mulVec ![init, 1] := by
  rw [← AffineSummary.matrix_list_prod, AffineSummary.matrix_act, foldall_affine h]

/-- A constant run in closed form. -/
theorem foldall_affine_replicate (h : AffineStep op coeff) (n : ℕ) (item : Item) (init : R) :
    foldall op (List.replicate n item) init =
      (coeff item).scale ^ n * init +
        (∑ i ∈ Finset.range n, (coeff item).scale ^ i) * (coeff item).offset := by
  rw [foldall_replicate h.represents]
  exact AffineSummary.act_pow (coeff item) n init

/-- Translation steps (`scale = 1`) may be reordered. -/
theorem foldall_perm_of_translations (h : AffineStep op coeff)
    (htr : ∀ item, (coeff item).scale = 1) {items₁ items₂ : List Item}
    (hp : items₁.Perm items₂) (init : R) :
    foldall op items₁ init = foldall op items₂ init :=
  foldall_perm h.represents hp
    (fun i _ j _ => AffineSummary.translations_commute _ (htr i) _ (htr j)) init

end Scalar

/-- Over a commutative semiring, scaling steps (`offset = 0`) may be
reordered. -/
theorem foldall_perm_of_scalings {Item : Type uItem} {R : Type*} [CommSemiring R]
    {op : Item → R → R} {coeff : Item → AffineSummary R} (h : AffineStep op coeff)
    (hsc : ∀ item, (coeff item).offset = 0) {items₁ items₂ : List Item}
    (hp : items₁.Perm items₂) (init : R) :
    foldall op items₁ init = foldall op items₂ init :=
  foldall_perm h.represents hp
    (fun i _ j _ => AffineSummary.scalings_commute _ (hsc i) _ (hsc j)) init

/-! ## PeTTa integer operators as affine steps -/

/-- `(+ item acc)` is the translation by `item`. -/
theorem add_step :
    AffineStep (fun item acc : ℤ => item + acc) AffineSummary.translation := by
  intro item acc
  rw [AffineSummary.act_translation, add_comm]

/-- `(* item acc)` is the scaling by `item`. -/
theorem mul_step : AffineStep (fun item acc : ℤ => item * acc) AffineSummary.scaling := by
  intro item acc
  rw [AffineSummary.act_scaling]

/-- `(- item acc)` has ratio `-1` and offset `item`. -/
theorem sub_step :
    AffineStep (fun item acc : ℤ => item - acc) (fun item => ⟨-1, item⟩) := by
  intro item acc
  simp only [AffineSummary.act]
  ring

/-- Sum folds may be reordered. -/
theorem sum_fold_perm {items₁ items₂ : List ℤ} (hp : items₁.Perm items₂) (init : ℤ) :
    foldall (fun item acc => item + acc) items₁ init =
      foldall (fun item acc => item + acc) items₂ init :=
  foldall_perm_of_translations add_step (fun _ => rfl) hp init

/-- Product folds may be reordered. -/
theorem product_fold_perm {items₁ items₂ : List ℤ} (hp : items₁.Perm items₂) (init : ℤ) :
    foldall (fun item acc => item * acc) items₁ init =
      foldall (fun item acc => item * acc) items₂ init :=
  foldall_perm_of_scalings mul_step (fun _ => rfl) hp init

/-- A constant subtraction run alternates between `init` and `item - init`. -/
theorem sub_fold_replicate (n : ℕ) (item init : ℤ) :
    foldall (fun item acc => item - acc) (List.replicate n item) init =
      if Even n then init else item - init := by
  rw [foldall_replicate sub_step.represents]
  change ((⟨-1, item⟩ : AffineSummary ℤ) ^ n).act init = _
  simp only [AffineSummary.act, AffineSummary.scale_pow,
    AffineSummary.offset_pow_of_scale_eq_neg_one (⟨-1, item⟩ : AffineSummary ℤ) rfl]
  rcases Nat.even_or_odd n with hn | hn
  · rw [if_pos hn, if_pos hn, hn.neg_one_pow]
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn), if_neg (Nat.not_even_iff_odd.mpr hn),
      hn.neg_one_pow]
    ring

/-! ## Fold-level controls -/

/-- Add one, then multiply by two, from `0`: the result depends on the
order. -/
theorem addOne_timesTwo_order_matters :
    foldall (fun (f : AffineSummary ℤ) acc => f.act acc)
        [AffineSummary.translation 1, AffineSummary.scaling 2] 0 = 2 ∧
      foldall (fun (f : AffineSummary ℤ) acc => f.act acc)
        [AffineSummary.scaling 2, AffineSummary.translation 1] 0 = 1 := by
  decide

/-- Without commutation, a permutation changes the fold: the commutation
hypothesis of `foldall_perm` cannot be dropped. -/
theorem perm_without_commutation_changes_fold :
    ∃ l₁ l₂ : List (AffineSummary ℤ), l₁.Perm l₂ ∧
      foldall (fun f acc => f.act acc) l₁ 0 ≠ foldall (fun f acc => f.act acc) l₂ 0 :=
  ⟨_, _, List.Perm.swap (AffineSummary.scaling 2) (AffineSummary.translation 1) [],
    by decide⟩

/-- PeTTa subtraction folds are order-sensitive. -/
theorem sub_fold_order_matters :
    foldall (fun item acc : ℤ => item - acc) [1, 2] 0 = 1 ∧
      foldall (fun item acc : ℤ => item - acc) [2, 1] 0 = -1 := by
  decide

/-- A reordered sum keeps its final value but not its trajectory: the
reordering license does not extend to observed intermediate states. -/
theorem reordered_sum_trajectory_differs :
    trajectory (fun item acc : ℤ => item + acc) [1, 2] 0 = [0, 1, 3] ∧
      trajectory (fun item acc : ℤ => item + acc) [2, 1] 0 = [0, 2, 3] := by
  decide

/-- A concrete bracketing: the fold of `+1, *2, +1` from `5` is the value of
the tree `+1 * (*2 * +1)`. -/
theorem bracketing_control :
    foldall (fun (f : AffineSummary ℤ) acc => f.act acc)
        (leaves (FreeMagma.of (AffineSummary.translation 1) *
          (FreeMagma.of (AffineSummary.scaling 2) *
            FreeMagma.of (AffineSummary.translation 1)))) 5 = 13 ∧
      (FreeMagma.lift id (FreeMagma.of (AffineSummary.translation (1 : ℤ)) *
          (FreeMagma.of (AffineSummary.scaling 2) *
            FreeMagma.of (AffineSummary.translation 1)))).act 5 = 13 := by
  decide

/-! ## The checked recognizer -/

section Recognizer

open Mettapedia.GSLT.AffineExpression

variable {n : ℕ}

/-- The source step of a fold body: evaluate the body with the answer row as
its inputs and the accumulator as `acc`. -/
def sourceStep (body : Expr n) : (Fin n → ℤ) → ℤ → ℤ :=
  fun row acc => body.eval row acc

theorem sourceFold_eq_foldall (body : Expr n) (rows : List (Fin n → ℤ)) (init : ℤ) :
    sourceFold body rows init = foldall (sourceStep body) rows init :=
  rfl

/-- **Recognizer contract, coefficient form.** An accepted body is affine in
the accumulator. Its coefficients are the compiled coefficient expressions,
which cannot mention the accumulator. -/
theorem compile_coeffs_sound {body : Expr n} {out : Form n} (h : compile body = some out)
    (row : Fin n → ℤ) (acc : ℤ) :
    body.eval row acc = out.scale.eval row * acc + out.offset.eval row :=
  (compile_sound body out h row acc).symm

/-- An accepted body is an affine fold step, with coefficients
`out.summary row`. -/
theorem affineStep_of_compile {body : Expr n} {out : Form n} (h : compile body = some out) :
    AffineStep (sourceStep body) out.summary :=
  fun row acc => (compile_sound body out h row acc).symm

/-- Every accepted body's source fold is the action of its ordered product
of coefficient summaries. -/
theorem sourceFold_eq_prod {body : Expr n} {out : Form n} (h : compile body = some out)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    sourceFold body rows init = (rows.map out.summary).prod.act init :=
  foldall_affine (affineStep_of_compile h) rows init

/-- Every accepted body's source trajectory is computed by a prefix scan of
coefficient summaries. -/
theorem sourceTrajectory_eq {body : Expr n} {out : Form n} (h : compile body = some out)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    trajectory (sourceStep body) rows init =
      ((rows.map out.summary).scanl (· * ·) 1).map (·.act init) :=
  trajectory_eq (affineStep_of_compile h).represents rows init

/-- Any bracketing of the rows computes the source fold of an accepted body. -/
theorem sourceFold_leaves {body : Expr n} {out : Form n} (h : compile body = some out)
    (t : FreeMagma (Fin n → ℤ)) (init : ℤ) :
    sourceFold body (leaves t) init = (FreeMagma.lift out.summary t).act init :=
  foldall_leaves (affineStep_of_compile h).represents t init

/-- Input-free constant value of coefficient syntax, if syntax alone
determines it. A product with a constant-zero factor is zero. -/
def constCoeff? : Coeff n → Option ℤ
  | .lit k => some k
  | .input _ => none
  | .bin op l r =>
      if op = .mul ∧ (constCoeff? l = some 0 ∨ constCoeff? r = some 0) then some 0
      else
        match constCoeff? l, constCoeff? r with
        | some x, some y => some (op.eval x y)
        | _, _ => none

theorem constCoeff?_sound {c : Coeff n} {k : ℤ} (h : constCoeff? c = some k)
    (row : Fin n → ℤ) : c.eval row = k := by
  induction c generalizing k with
  | lit k' =>
      simp only [constCoeff?, Option.some.injEq] at h
      exact h
  | input i => simp [constCoeff?] at h
  | bin op l r ihl ihr =>
      simp only [constCoeff?] at h
      split_ifs at h with hzero
      · cases h
        obtain ⟨rfl, hl | hr⟩ := hzero
        · simp [Coeff.eval, Op.eval, ihl hl]
        · simp [Coeff.eval, Op.eval, ihr hr]
      · split at h
        · rename_i x y hx hy
          cases h
          simp [Coeff.eval, ihl hx, ihr hy]
        · cases h

/-- **Reordering admission.** A compiled body may have its answers permuted
when its scale is constantly `1` (a translation) or its offset is constantly
`0` (a scaling). -/
def reorderable (out : Form n) : Bool :=
  constCoeff? out.scale == some 1 || constCoeff? out.offset == some 0

theorem reorderable_commute {out : Form n} (hr : reorderable out = true)
    (row row' : Fin n → ℤ) : Commute (out.summary row) (out.summary row') := by
  simp only [reorderable, Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with hs | ho
  · exact AffineSummary.translations_commute _ (constCoeff?_sound hs row) _
      (constCoeff?_sound hs row')
  · exact AffineSummary.scalings_commute _ (constCoeff?_sound ho row) _
      (constCoeff?_sound ho row')

/-- **Reordering admission is sound.** -/
theorem reorder_sound {body : Expr n} {out : Form n} (h : compile body = some out)
    (hr : reorderable out = true) {rows₁ rows₂ : List (Fin n → ℤ)}
    (hp : rows₁.Perm rows₂) (init : ℤ) :
    sourceFold body rows₁ init = sourceFold body rows₂ init :=
  foldall_perm (affineStep_of_compile h).represents hp
    (fun row _ row' _ => reorderable_commute hr row row') init

/-! ### Recognizer controls -/

/-- `acc + 3 * item` -/
def accPlusThreeItem : Expr 1 := .bin .add .acc (.bin .mul (.lit 3) (.input 0))

/-- `-acc + 3 * item`, with PeTTa's binary minus: `(0 - acc) + 3 * item` -/
def negAccPlusThreeItem : Expr 1 :=
  .bin .add (.bin .sub (.lit 0) .acc) (.bin .mul (.lit 3) (.input 0))

/-- `item * acc + 1` -/
def itemTimesAccPlusOne : Expr 1 := .bin .add (.bin .mul (.input 0) .acc) (.lit 1)

/-- `2 * acc + item` -/
def twoAccPlusItem : Expr 1 := .bin .add (.bin .mul (.lit 2) .acc) (.input 0)

/-- `acc * acc + item` -/
def accSquaredPlusItem : Expr 1 := .bin .add (.bin .mul .acc .acc) (.input 0)

/-- `(acc + 1) * (acc + 1) - acc * acc`, which denotes `2 * acc + 1`. -/
def expandedSquareDifference : Expr 1 :=
  .bin .sub (.bin .mul (.bin .add .acc (.lit 1)) (.bin .add .acc (.lit 1)))
    (.bin .mul .acc .acc)

/-- Reading the compiled coefficients of an accepted body. -/
theorem eval_eq_of_compile {body : Expr n} {out : Form n} (h : compile body = some out)
    {a b : (Fin n → ℤ) → ℤ} (ha : ∀ row, out.scale.eval row = a row)
    (hb : ∀ row, out.offset.eval row = b row) (row : Fin n → ℤ) (acc : ℤ) :
    body.eval row acc = a row * acc + b row := by
  rw [compile_coeffs_sound h, ha, hb]

theorem accPlusThreeItem_affine (row : Fin 1 → ℤ) (acc : ℤ) :
    accPlusThreeItem.eval row acc = 1 * acc + 3 * row 0 :=
  eval_eq_of_compile (body := accPlusThreeItem) (a := fun _ => 1) (b := fun r => 3 * r 0) rfl
    (fun _ => by simp [Form.scale, Coeff.eval, Op.eval])
    (fun _ => by simp [Form.offset, Coeff.eval, Op.eval]) row acc

theorem negAccPlusThreeItem_affine (row : Fin 1 → ℤ) (acc : ℤ) :
    negAccPlusThreeItem.eval row acc = -1 * acc + 3 * row 0 :=
  eval_eq_of_compile (body := negAccPlusThreeItem) (a := fun _ => -1) (b := fun r => 3 * r 0) rfl
    (fun _ => by simp [Form.scale, Coeff.eval, Op.eval])
    (fun _ => by simp [Form.offset, Coeff.eval, Op.eval]) row acc

theorem itemTimesAccPlusOne_affine (row : Fin 1 → ℤ) (acc : ℤ) :
    itemTimesAccPlusOne.eval row acc = row 0 * acc + 1 :=
  eval_eq_of_compile (body := itemTimesAccPlusOne) (a := fun r => r 0) (b := fun _ => 1) rfl
    (fun _ => by simp [Form.scale, Coeff.eval, Op.eval])
    (fun _ => by simp [Form.offset, Coeff.eval, Op.eval]) row acc

theorem twoAccPlusItem_affine (row : Fin 1 → ℤ) (acc : ℤ) :
    twoAccPlusItem.eval row acc = 2 * acc + row 0 :=
  eval_eq_of_compile (body := twoAccPlusItem) (a := fun _ => 2) (b := fun r => r 0) rfl
    (fun _ => by simp [Form.scale, Coeff.eval, Op.eval])
    (fun _ => by simp [Form.offset, Coeff.eval, Op.eval]) row acc

/-- Only the translation among the four accepted examples is licensed for
reordering. -/
theorem examples_reorderable :
    (compile accPlusThreeItem).map reorderable = some true ∧
      (compile negAccPlusThreeItem).map reorderable = some false ∧
      (compile itemTimesAccPlusOne).map reorderable = some false ∧
      (compile twoAccPlusItem).map reorderable = some false := by
  decide

/-- PeTTa's `(+ item acc)` and `(* item acc)` are admitted for reordering;
`(- item acc)` is not. -/
theorem operator_bodies_reorderable :
    (compile (.bin .add (.input 0) .acc : Expr 1)).map reorderable = some true ∧
      (compile (.bin .mul (.input 0) .acc : Expr 1)).map reorderable = some true ∧
      (compile (.bin .sub (.input 0) .acc : Expr 1)).map reorderable = some false := by
  decide

/-- A reorderable body in use: permuting the answers of `acc + 3 * item`
does not change the fold. -/
theorem accPlusThreeItem_perm {rows₁ rows₂ : List (Fin 1 → ℤ)} (hp : rows₁.Perm rows₂)
    (init : ℤ) :
    sourceFold accPlusThreeItem rows₁ init = sourceFold accPlusThreeItem rows₂ init :=
  reorder_sound rfl (by decide) hp init

/-- `acc * acc + item` is rejected. -/
theorem accSquaredPlusItem_rejected : compile accSquaredPlusItem = none := rfl

/-- `acc * acc + item` is not affine in the accumulator for any
coefficients. -/
theorem accSquaredPlusItem_not_affine :
    ¬ ∃ a b : (Fin 1 → ℤ) → ℤ, ∀ row acc,
      accSquaredPlusItem.eval row acc = a row * acc + b row := by
  rintro ⟨a, b, h⟩
  have h0 := h 0 0
  have h1 := h 0 1
  have h2 := h 0 2
  simp only [accSquaredPlusItem, Expr.eval, Op.eval, Pi.zero_apply] at h0 h1 h2
  omega

/-- The recognizer is conservative: this body denotes `2 * acc + 1` but is
rejected, so admission falls back to source execution. -/
theorem expandedSquareDifference_rejected_but_affine :
    compile expandedSquareDifference = none ∧
      ∀ row acc, expandedSquareDifference.eval row acc = 2 * acc + 1 := by
  refine ⟨rfl, fun row acc => ?_⟩
  simp only [expandedSquareDifference, Expr.eval, Op.eval]
  ring

end Recognizer

/-! ## Tropical linear-state folds: edge relaxation -/

section Tropical

open Tropical Matrix

variable {ι : Type*} [DecidableEq ι] {T : Type*} [LinearOrderedAddCommMonoidWithTop T]

/-- Relax the edge `u → v` of weight `w`. In min-plus notation this is
`d v := min (d v) (d u + w)`: tropical `+` is `min` and tropical `*` is `+`. -/
def relax (u v : ι) (w : T) (d : ι → Tropical T) : ι → Tropical T :=
  Function.update d v (d v + trop w * d u)

/-- A weighted directed edge. -/
structure Edge (ι T : Type*) where
  src : ι
  dst : ι
  weight : T

/-- The fold step of one relaxation pass. -/
def relaxStep (e : Edge ι T) (d : ι → Tropical T) : ι → Tropical T :=
  relax e.src e.dst e.weight d

variable [Fintype ι]

/-- Edge relaxation as a linear-state update: the tropical identity plus one
entry. -/
def relaxation (u v : ι) (w : T) : MatrixAffineSummary ι (Tropical T) :=
  ⟨1 + Matrix.single v u (trop w), 0⟩

theorem act_relaxation (u v : ι) (w : T) (d : ι → Tropical T) :
    (relaxation u v w).act d = relax u v w d := by
  ext i
  simp only [relaxation, relax, MatrixAffineSummary.act, add_mulVec, one_mulVec,
    single_mulVec, add_zero, Pi.add_apply, Function.update_apply, Pi.zero_apply]
  split_ifs with hi
  · subst hi
    rfl
  · exact add_zero (d i)

/-- The coefficient of one relaxation step. -/
def relaxCoeff (e : Edge ι T) : MatrixAffineSummary ι (Tropical T) :=
  relaxation e.src e.dst e.weight

theorem relaxStep_represents : Represents (relaxStep (ι := ι) (T := T)) relaxCoeff :=
  fun e d => (act_relaxation e.src e.dst e.weight d).symm

/-- **A relaxation pass is one linear-state product.** Relaxing an ordered
edge list equals applying the ordered product of the relaxation matrices. -/
theorem relaxation_pass_eq (edges : List (Edge ι T)) (d : ι → Tropical T) :
    foldall relaxStep edges d = (edges.map relaxCoeff).prod.act d :=
  foldall_eq relaxStep_represents edges d

/-- Three vertices, source `0`: edges `0 → 1` (4), `1 → 2` (1), `0 → 2` (7). -/
def exampleEdges : List (Edge (Fin 3) ℕ∞) := [⟨0, 1, 4⟩, ⟨1, 2, 1⟩, ⟨0, 2, 7⟩]

/-- Distance `0` at the source and `⊤` (unreached) elsewhere. -/
def exampleStart : Fin 3 → Tropical ℕ∞ := ![trop 0, trop ⊤, trop ⊤]

/-- In this order one pass finds the shortest distances `0, 4, 5`. -/
theorem relaxation_pass_control :
    foldall relaxStep exampleEdges exampleStart = ![trop 0, trop 4, trop 5] := by
  decide

/-- The same distances, computed as one product of relaxation matrices. -/
theorem relaxation_product_control :
    (exampleEdges.map relaxCoeff).prod.act exampleStart = ![trop 0, trop 4, trop 5] := by
  rw [← relaxation_pass_eq]
  exact relaxation_pass_control

/-- Reversing the pass changes the result: `0 → 2` is relaxed before `1` is
reached, so one pass leaves the distance `7`. -/
theorem relaxation_order_matters :
    foldall relaxStep exampleEdges.reverse exampleStart = ![trop 0, trop 4, trop 7] := by
  decide

end Tropical

end Mettapedia.GSLT.Dynamics.AffineFoldCompilation
