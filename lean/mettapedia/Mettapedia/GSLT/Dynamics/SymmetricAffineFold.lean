import Mettapedia.GSLT.Dynamics.AffineFoldCompilation

/-!
# Symmetric affine folds: translations and scalings

An ordered fold is *symmetric* in its items when no permutation of the items
changes its value. Equivalently, the value is a function of the multiset of
items. `AffineFoldCompilation.foldall_perm` licenses permutation when the
coefficients commute. This file gives the two basic commuting families closed
forms that exhibit the value as an explicit function of the multiset.

* **Translations** (`scale = 1`): the fold adds the sum of the offsets
  (`foldall_eq_add_sum`). For `acc ↦ acc + (c * item + d)` the value is
  `init + c * Σ items + d * #items` (`foldall_add_mul_add`).
* **Scalings** (`offset = 0`), over a commutative semiring: the fold
  multiplies by the product of the scales (`foldall_eq_mul_prod`). For
  `acc ↦ item * acc` the value is `init * Π items` (`foldall_item_mul`). For
  the item-free `acc ↦ c * acc` it is `init * c ^ #items`
  (`foldall_const_mul`).

The item-level closed forms are stated with the multiset `(items : Multiset R)`,
so the right-hand side depends on nothing else. The permutation laws
`foldall_perm_of_translations` and `foldall_perm_of_scalings` follow from
them.

For compiled bodies, the two syntactic admissions of
`AffineFoldCompilation.reorderable` give the closed forms over the multiset of
answer rows: compiled scale syntactically `1` (`sourceFold_of_scale_eq_one`),
or compiled offset syntactically `0` (`sourceFold_of_offset_eq_zero`). The
source bodies `acc + (c * item + d)`, `item * acc` and `c * acc` pass these
admissions, with the expected closed forms (`sourceFold_addMulAdd`,
`sourceFold_itemMul`, `sourceFold_constMul`).

## Controls

* `addMulAdd_control`: one multiset in two orders, with the closed-form value.
* `twoAccPlusItem_not_symmetric`: the body `2 * acc + item` is admitted by the
  compiler but fails both admissions, and the multiset `{1, 2}` folds to `4`
  in one order and `5` in the other.
* `sourceFold_oddHomothety_perm`, `oddHomothety_not_admitted`: the admissions
  are sufficient, not necessary. The body `(2 * item + 1) * acc + item` is,
  for every item, a homothety with centre `-1/2`. Its summaries commute, so its
  fold is symmetric for every stream, yet it fails both admissions.

## What is not covered

* **Other commuting families.** Homotheties with a common centre commute
  (`AffineSummary.commute_homothety`), and over `ℤ` the centre need not be an
  integer (`oddHomothety`). No admission or closed form for them is given
  here.
* **Intermediate accumulators.** Only the final value is symmetric. The
  trajectory is not (`reordered_sum_trajectory_differs`).
* **Machine arithmetic.** The laws are exact. Sums and products of many items
  need overflow guards in the native realization.

## Mapping to CeTTa fold admission

A route that holds only the multiset of answers, for instance a count table
produced by a conjunction, cannot replay the answer order. It may still
compute a `foldall` whose compiled body passes one of the two admissions. For
a translation it computes `init + Σ offset(row)`, and for a scaling
`init * Π scale(row)`, each summed or multiplied over the multiset with
multiplicities. For the literal bodies above this needs only the count, the
sum and the product of the item values. A body that fails both admissions gets
no license here to use the multiset alone and falls back to the ordered
stream, even though some such bodies are symmetric (`oddHomothety`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SymmetricAffineFold

open Mettapedia.Algebra Mettapedia.GSLT.Dynamics.AffineFoldCompilation

/-! ## Products of translations and of scalings -/

section Generic

variable {Item : Type*} {R : Type*}

/-- A product of translations is the translation by the sum of the offsets. -/
theorem prod_map_translation [Semiring R] (b : Item → R) (items : List Item) :
    (items.map fun i => AffineSummary.translation (b i)).prod =
      AffineSummary.translation (items.map b).sum := by
  induction items with
  | nil => rfl
  | cons i items ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons,
        AffineSummary.translation_add]

/-- Over a commutative semiring, a product of scalings is the scaling by the
product of the scales. -/
theorem prod_map_scaling [CommSemiring R] (a : Item → R) (items : List Item) :
    (items.map fun i => AffineSummary.scaling (a i)).prod =
      AffineSummary.scaling (items.map a).prod := by
  induction items with
  | nil => rfl
  | cons i items ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, mul_comm (a i),
        AffineSummary.scaling_mul]

/-- **Translation folds.** A fold of translation steps adds the sum of the
offsets to the initial accumulator. -/
theorem foldall_eq_add_sum [Semiring R] {op : Item → R → R} {coeff : Item → AffineSummary R}
    (h : AffineStep op coeff) (htr : ∀ i, (coeff i).scale = 1) (items : List Item) (init : R) :
    foldall op items init = init + (items.map fun i => (coeff i).offset).sum := by
  rw [foldall_affine h,
    List.map_congr_left fun i _ => AffineSummary.eq_translation_of_mem (htr i),
    prod_map_translation, AffineSummary.act_translation]

/-- **Scaling folds.** Over a commutative semiring, a fold of scaling steps
multiplies the initial accumulator by the product of the scales. -/
theorem foldall_eq_mul_prod [CommSemiring R] {op : Item → R → R}
    {coeff : Item → AffineSummary R} (h : AffineStep op coeff)
    (hsc : ∀ i, (coeff i).offset = 0) (items : List Item) (init : R) :
    foldall op items init = init * (items.map fun i => (coeff i).scale).prod := by
  have hc : ∀ i ∈ items, coeff i = AffineSummary.scaling (coeff i).scale :=
    fun i _ => AffineSummary.ext rfl (hsc i)
  rw [foldall_affine h, List.map_congr_left hc, prod_map_scaling, AffineSummary.act_scaling,
    mul_comm]

end Generic

/-! ## Item-level closed forms -/

section Items

variable {R : Type*} [CommSemiring R]

/-- The sum of `c * item + d` over a list is `c * Σ items + d * #items`. -/
theorem sum_map_mul_add (c d : R) (items : List R) :
    (items.map fun i => c * i + d).sum = c * items.sum + d * items.length := by
  induction items with
  | nil => simp
  | cons i items ih =>
      rw [List.map_cons, List.sum_cons, ih, List.sum_cons, List.length_cons, Nat.cast_succ]
      ring

/-- `acc ↦ acc + (c * item + d)`: the fold adds `c` times the sum of the items
and `d` times their number. -/
theorem foldall_add_mul_add (c d : R) (items : List R) (init : R) :
    foldall (fun item acc => acc + (c * item + d)) items init =
      init + c * (items : Multiset R).sum + d * Multiset.card (items : Multiset R) := by
  rw [foldall_eq_add_sum (coeff := fun item => AffineSummary.translation (c * item + d))
      (fun _ _ => (AffineSummary.act_translation _ _).symm) (fun _ => rfl),
    Multiset.sum_coe, Multiset.coe_card, add_assoc]
  exact congrArg (init + ·) (sum_map_mul_add c d items)

/-- `acc ↦ item * acc`: the fold multiplies by the product of the items. -/
theorem foldall_item_mul (items : List R) (init : R) :
    foldall (fun item acc => item * acc) items init = init * (items : Multiset R).prod := by
  rw [foldall_eq_mul_prod (coeff := AffineSummary.scaling)
      (fun _ _ => (AffineSummary.act_scaling _ _).symm) (fun _ => rfl),
    Multiset.prod_coe]
  simp only [AffineSummary.scaling_scale, List.map_id']

/-- `acc ↦ c * acc`, item-free: the fold multiplies by `c` once per item. -/
theorem foldall_const_mul {Item : Type*} (c : R) (items : List Item) (init : R) :
    foldall (fun _ acc => c * acc) items init =
      init * c ^ Multiset.card (items : Multiset Item) := by
  rw [foldall_eq_mul_prod (coeff := fun _ => AffineSummary.scaling c)
      (fun _ _ => (AffineSummary.act_scaling _ _).symm) (fun _ => rfl),
    Multiset.coe_card]
  simp only [AffineSummary.scaling_scale, List.map_const', List.prod_replicate]

end Items

/-! ## Compiled bodies -/

section Compiled

open Mettapedia.GSLT.AffineExpression

variable {n : ℕ}

/-- A compiled body whose scale is syntactically the constant `1` is a
translation. Its source fold adds the offsets of the answer rows, counted with
multiplicity. -/
theorem sourceFold_of_scale_eq_one {body : Expr n} {out : Form n}
    (h : compile body = some out) (hs : constCoeff? out.scale = some 1)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    sourceFold body rows init =
      init + ((rows : Multiset (Fin n → ℤ)).map out.offset.eval).sum := by
  rw [Multiset.map_coe, Multiset.sum_coe]
  exact foldall_eq_add_sum (affineStep_of_compile h) (fun row => constCoeff?_sound hs row)
    rows init

/-- A compiled body whose offset is syntactically the constant `0` is a
scaling. Its source fold multiplies by the scales of the answer rows, counted
with multiplicity. -/
theorem sourceFold_of_offset_eq_zero {body : Expr n} {out : Form n}
    (h : compile body = some out) (ho : constCoeff? out.offset = some 0)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    sourceFold body rows init =
      init * ((rows : Multiset (Fin n → ℤ)).map out.scale.eval).prod := by
  rw [Multiset.map_coe, Multiset.prod_coe]
  exact foldall_eq_mul_prod (affineStep_of_compile h) (fun row => constCoeff?_sound ho row)
    rows init

/-- `acc + (c * item + d)`. -/
def addMulAdd (c d : ℤ) : Expr 1 :=
  .bin .add .acc (.bin .add (.bin .mul (.lit c) (.input 0)) (.lit d))

/-- `item * acc`. -/
def itemMul : Expr 1 := .bin .mul (.input 0) .acc

/-- `c * acc`. -/
def constMul (c : ℤ) : Expr 1 := .bin .mul (.lit c) .acc

/-- The source fold of `acc + (c * item + d)`: `init + c * Σ items + d * #items`
over the multiset of answer rows. -/
theorem sourceFold_addMulAdd (c d : ℤ) (rows : List (Fin 1 → ℤ)) (init : ℤ) :
    sourceFold (addMulAdd c d) rows init =
      init + c * ((rows : Multiset (Fin 1 → ℤ)).map (· 0)).sum +
        d * Multiset.card (rows : Multiset (Fin 1 → ℤ)) := by
  rw [sourceFold_of_scale_eq_one rfl rfl, Multiset.map_coe, Multiset.map_coe, Multiset.sum_coe,
    Multiset.sum_coe, Multiset.coe_card, add_assoc,
    ← List.length_map (fun row : Fin 1 → ℤ => row 0), ← sum_map_mul_add, List.map_map]
  simp only [Form.offset, Coeff.eval, Op.eval, zero_add, Function.comp_def]

/-- The source fold of `item * acc`: `init * Π items` over the multiset of
answer rows. -/
theorem sourceFold_itemMul (rows : List (Fin 1 → ℤ)) (init : ℤ) :
    sourceFold itemMul rows init = init * ((rows : Multiset (Fin 1 → ℤ)).map (· 0)).prod := by
  rw [sourceFold_of_offset_eq_zero rfl rfl]
  simp only [Form.scale, Coeff.eval, Op.eval, mul_one]

/-- The source fold of `c * acc`: `init * c ^ #items`. -/
theorem sourceFold_constMul (c : ℤ) (rows : List (Fin 1 → ℤ)) (init : ℤ) :
    sourceFold (constMul c) rows init =
      init * c ^ Multiset.card (rows : Multiset (Fin 1 → ℤ)) := by
  rw [sourceFold_of_offset_eq_zero (body := constMul c) rfl (by simp [Form.offset, constCoeff?]),
    Multiset.map_coe, Multiset.prod_coe, Multiset.coe_card]
  simp only [Form.scale, Coeff.eval, Op.eval, mul_one, List.map_const', List.prod_replicate]

/-! ### Controls -/

/-- One multiset, two orders, one value: `acc + (3 * item + 1)` over the items
`1, 2, 4` from `10` gives `10 + 3 * 7 + 3 = 34`. -/
theorem addMulAdd_control :
    sourceFold (addMulAdd 3 1) [![1], ![2], ![4]] 10 = 34 ∧
      sourceFold (addMulAdd 3 1) [![4], ![1], ![2]] 10 = 34 := by
  decide

/-- `2 * acc + item` is admitted but is neither a translation nor a scaling. Its
fold is not a function of the multiset of items: `{1, 2}` gives `4` in one
order and `5` in the other. -/
theorem twoAccPlusItem_not_symmetric :
    (compile twoAccPlusItem).map reorderable = some false ∧
      sourceFold twoAccPlusItem [![1], ![2]] 0 = 4 ∧
      sourceFold twoAccPlusItem [![2], ![1]] 0 = 5 := by
  decide

/-- `(2 * item + 1) * acc + item`: for every item, the homothety with centre
`-1/2` and ratio `2 * item + 1`. -/
def oddHomothety : Expr 1 :=
  .bin .add (.bin .mul (.bin .add (.bin .mul (.lit 2) (.input 0)) (.lit 1)) .acc) (.input 0)

/-- The compiled form of `(2 * item + 1) * acc + item`. -/
def oddHomothetyForm : Form 1 :=
  .affine (.bin .add (.bin .mul (.bin .add (.bin .mul (.lit 2) (.input 0)) (.lit 1)) (.lit 1))
      (.lit 0))
    (.bin .add (.bin .mul (.bin .add (.bin .mul (.lit 2) (.input 0)) (.lit 1)) (.lit 0))
      (.input 0))

theorem compile_oddHomothety : compile oddHomothety = some oddHomothetyForm := rfl

/-- All summaries of `oddHomothety` commute: they share the centre `-1/2`. -/
theorem oddHomothety_commute (row row' : Fin 1 → ℤ) :
    Commute (oddHomothetyForm.summary row) (oddHomothetyForm.summary row') := by
  rw [AffineSummary.commute_iff_of_commRing]
  simp only [oddHomothetyForm, Form.summary, Form.scale, Form.offset, Coeff.eval, Op.eval]
  ring

/-- The admissions are sufficient, not necessary. `oddHomothety` passes
neither, yet its fold is symmetric for every stream. -/
theorem sourceFold_oddHomothety_perm {rows₁ rows₂ : List (Fin 1 → ℤ)} (hp : rows₁.Perm rows₂)
    (init : ℤ) : sourceFold oddHomothety rows₁ init = sourceFold oddHomothety rows₂ init :=
  foldall_perm (affineStep_of_compile compile_oddHomothety).represents hp
    (fun row _ row' _ => oddHomothety_commute row row') init

/-- `oddHomothety` fails both admissions, and `{1, 2}` folds to `7` in both
orders. -/
theorem oddHomothety_not_admitted :
    (compile oddHomothety).map reorderable = some false ∧
      sourceFold oddHomothety [![1], ![2]] 0 = 7 ∧
      sourceFold oddHomothety [![2], ![1]] 0 = 7 := by
  decide

end Compiled

end Mettapedia.GSLT.Dynamics.SymmetricAffineFold
