import Mettapedia.Algebra.AffineSummaryMap
import Mettapedia.GSLT.Dynamics.AffineFoldCompilation
import Mathlib.Data.ZMod.Basic

/-!
# Modular affine folds: PeTTa steps `(% e m)` computed in `ZMod m`

A PeTTa fold whose step body is `(% e m)` evaluates the dividend `e` on the
answer row and the accumulator, then reduces by `m`. PeTTa's `%` is SWI-Prolog
`mod`, the remainder of floor division, whose sign follows the divisor. In Lean
that is `Int.fmod`. For a nonnegative divisor it coincides with Lean's `%` on
`ℤ` (`Int.emod`). `modStep body m` is this step, and the fold is
`AffineFoldCompilation.foldall`, which applies the first answer first, as
`(op item acc)`.

## What is proved

For every dividend `body : Expr n` (admitted by the affine compiler or not) and
every modulus `m : ℤ`:

* `Expr.eval_modEq`: the source language is a congruence modulo `m`, in its
  inputs and in its accumulator, because it has only `+`, `-` and `*`.
* `foldall_modStep_modEq`: reducing at every step does not change the residue
  class of the fold.
* `foldall_modStep_of_ne_nil`: **reduce once at the end.** On a nonempty
  stream, the modular fold is `Int.fmod` of the unreduced source fold. This
  holds for negative and zero divisors too.

For an admitted dividend (`compile body = some out`) and a natural modulus
`m`, reduction to `ZMod m` is a ring homomorphism, and
`AffineSummary.map` carries every row's summary to `ZMod m`.
`modularRoute out m rows init` is the value the route computes: the ordered
product of the reduced summaries, acting on the reduced initial accumulator,
read as the canonical residue in `[0, m)`.

* `cast_foldall_modStep`: the residue of the modular fold is that product's
  action, for every stream, the empty one included.
* `foldall_modStep_eq_modularRoute` (main theorem): for `0 < m` and a
  nonempty stream, the modular fold **equals** `modularRoute`.
  `foldl_emod_eq_modularRoute` states it with Lean's `%`, and
  `foldall_modStep_eq` gives the piecewise form, in which the empty stream
  returns `init` unreduced.
* `mem_tail_trajectory_modStep`: every accumulator after at least one step
  lies in `[0, m)`, for every body.
* `getElem_trajectory_modStep`: every such accumulator is the route of the
  corresponding prefix, so a prefix scan in `ZMod m` computes the trajectory.
* `foldall_modStep_replicate`, `foldall_modStep_replicate_closed`: `k ≥ 1`
  copies of one row give the `k`-th power of its reduced summary, and its
  closed form as a geometric sum in `ZMod m`.
* `modularRoute_reduce_inputs`: the route depends only on the residues of the
  inputs and of the initial accumulator.

The monoid laws of `Mettapedia.Algebra.ActionFold` apply to the reduced
summaries in `AffineSummary (ZMod m)` without change. They cover every
bracketing, the blocked scan, and powers by repeated squaring.

## Controls

* `decimal_residue`: `(% (+ (* 10 acc) item) 7)` over the digits `1, 2, 3`
  gives `4 = 123 mod 7`, both by the source fold and by the route.
* `empty_stream_unreduced`: on the empty stream the fold is `init` even when
  `init ∉ [0, m)`, while the route returns a residue. The nonempty hypothesis
  of the main theorem cannot be dropped.
* `item_modulus_has_no_fixed_ring`: with `(% acc item)` the modulus changes
  with the item, and no fixed `m` reproduces the fold.
* `negative_modulus_outside_route`: PeTTa's `(% 1 -3)` is `-2`, outside
  `[0, 3)`. The reduce-at-the-end law still holds for a negative divisor, but
  the residue route does not apply.
* `truncated_remainder_outside_route`: HE and Prime `%` is the truncating
  remainder (`Int.tmod`), whose sign follows the dividend. The route is valid
  only for floor modulo.

## What is not covered

* **Machine arithmetic.** All laws are exact. After reduction the route
  multiplies only residues, and a product of two residues is below `m²`.
  Overflow of such products, and of coefficient evaluation before reduction,
  needs guards in the native realization.
* **The modulus.** It must be a positive integer literal. Zero, negative and
  item-dependent moduli are outside the route. Only a top-level `%` is
  recognized; `%` nested inside the dividend has no constructor in `Expr`.
* **Dialect.** The route is valid for PeTTa's floor modulo. Truncating
  remainder (HE, Prime) needs its own admission.
* **Effects, errors, fuel.** As in `AffineFoldCompilation`, the source
  language is pure and no statement concerns evaluation cost.

## Mapping to CeTTa fold admission

The modular route admits a PeTTa `foldall` whose step body is `%` applied to
a dividend and a positive integer literal `m`, when the dividend decodes to
`Expr n` and `compile` accepts it. Execution evaluates the compiled
coefficients per answer, reduces them modulo `m` (inputs may be reduced
first), combines the reduced summaries in `ZMod m` in answer order, and
returns the canonical residue. An empty answer stream returns the initial
accumulator unchanged. The ordered-product laws of `AffineFoldCompilation`
(bracketing, blocked scans, powers) license the same parallel strategies in
`ZMod m`. Permuting answers still requires commuting summaries.
-/

set_option autoImplicit false

open Mettapedia.Algebra Mettapedia.GSLT.AffineExpression
open Mettapedia.GSLT.Dynamics.AffineFoldCompilation

namespace Mettapedia.GSLT.AffineExpression

variable {n : ℕ}

/-- Coefficient syntax is a congruence modulo `m` in its inputs. -/
theorem Coeff.eval_modEq (c : Coeff n) {m : ℤ} {env env' : Fin n → ℤ}
    (henv : ∀ i, env i ≡ env' i [ZMOD m]) : c.eval env ≡ c.eval env' [ZMOD m] := by
  induction c with
  | lit k => exact Int.ModEq.refl k
  | input i => exact henv i
  | bin op l r ihl ihr =>
      cases op
      · exact ihl.add ihr
      · exact ihl.sub ihr
      · exact ihl.mul ihr

/-- Every source body is a congruence modulo `m` in its inputs and its
accumulator, admitted or not: the language has only `+`, `-` and `*`. -/
theorem Expr.eval_modEq (e : Expr n) {m : ℤ} {env env' : Fin n → ℤ}
    (henv : ∀ i, env i ≡ env' i [ZMOD m]) {a b : ℤ} (h : a ≡ b [ZMOD m]) :
    e.eval env a ≡ e.eval env' b [ZMOD m] := by
  induction e with
  | lit k => exact Int.ModEq.refl k
  | input i => exact henv i
  | acc => exact h
  | bin op l r ihl ihr =>
      cases op
      · exact ihl.add ihr
      · exact ihl.sub ihr
      · exact ihl.mul ihr

end Mettapedia.GSLT.AffineExpression

namespace Mettapedia.GSLT.Dynamics.ModularAffineFold

variable {n : ℕ}

/-! ## PeTTa's `%`: floor modulo -/

/-- Floor modulo is congruent to its dividend, for every divisor. -/
theorem fmod_modEq (a m : ℤ) : Int.fmod a m ≡ a [ZMOD m] :=
  Int.modEq_iff_dvd.mpr ⟨Int.fdiv a m, by rw [Int.fmod_def]; ring⟩

/-- Floor modulo depends only on the residue class of the dividend. -/
theorem fmod_eq_of_modEq {a b m : ℤ} (h : a ≡ b [ZMOD m]) : Int.fmod a m = Int.fmod b m := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  rw [eq_add_of_sub_eq' hk, Int.add_mul_fmod_self_left]

/-- For a positive divisor, floor modulo lands in `[0, m)`. -/
theorem fmod_nonneg_lt {m : ℤ} (hm : 0 < m) (a : ℤ) : 0 ≤ Int.fmod a m ∧ Int.fmod a m < m :=
  ⟨Int.fmod_nonneg_of_pos a hm, Int.fmod_lt_of_pos a hm⟩

/-! ## The modular step -/

/-- The step of a body `(% e m)`: evaluate the dividend `e` on the answer row
and the accumulator, then reduce with PeTTa's `%`, which is floor modulo. -/
def modStep (body : Expr n) (m : ℤ) (row : Fin n → ℤ) (acc : ℤ) : ℤ :=
  Int.fmod (body.eval row acc) m

/-- For a nonnegative divisor the step reduces with Lean's `%`. -/
theorem modStep_of_nonneg (body : Expr n) {m : ℤ} (hm : 0 ≤ m) (row : Fin n → ℤ) (acc : ℤ) :
    modStep body m row acc = body.eval row acc % m :=
  Int.fmod_eq_emod_of_nonneg _ hm

/-- **Congruence.** Reducing at every step keeps the residue class of the
unreduced source fold, for every body and every modulus. -/
theorem foldall_modStep_modEq (body : Expr n) (m : ℤ) (rows : List (Fin n → ℤ)) {a b : ℤ}
    (h : a ≡ b [ZMOD m]) : foldall (modStep body m) rows a ≡ sourceFold body rows b [ZMOD m] := by
  induction rows generalizing a b with
  | nil => exact h
  | cons row rows ih =>
      exact ih ((fmod_modEq _ m).trans (body.eval_modEq (fun _ => Int.ModEq.refl _) h))

/-- **Reduce once at the end.** On a nonempty stream, reducing at every step
equals reducing the unreduced source fold once. This holds for every body and
every divisor, negative and zero included. -/
theorem foldall_modStep_of_ne_nil (body : Expr n) (m : ℤ) {rows : List (Fin n → ℤ)}
    (hrows : rows ≠ []) (init : ℤ) :
    foldall (modStep body m) rows init = Int.fmod (sourceFold body rows init) m := by
  rw [← List.dropLast_append_getLast hrows, foldall_append, sourceFold, List.foldl_append]
  exact fmod_eq_of_modEq (body.eval_modEq (fun _ => Int.ModEq.refl _)
    (foldall_modStep_modEq body m _ (Int.ModEq.refl init)))

/-- After at least one step, every accumulator is a residue in `[0, m)`, for
every body and every positive divisor. -/
theorem mem_tail_trajectory_modStep (body : Expr n) {m : ℤ} (hm : 0 < m)
    (rows : List (Fin n → ℤ)) (init : ℤ) :
    ∀ z ∈ (trajectory (modStep body m) rows init).tail, 0 ≤ z ∧ z < m := by
  induction rows generalizing init with
  | nil => simp [trajectory]
  | cons row rows ih =>
      intro z hz
      have htail : (trajectory (modStep body m) (row :: rows) init).tail =
          trajectory (modStep body m) rows (modStep body m row init) := by
        simp only [trajectory, List.scanl_cons, List.tail_cons]
      rw [htail, trajectory_eq_cons_tail] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact fmod_nonneg_lt hm _
      · exact ih _ z hz

/-! ## The route in `ZMod m` -/

/-- The modular route of a compiled body: reduce each row's summary to
`ZMod m`, take the ordered product, act on the reduced initial accumulator, and
read the canonical representative, which lies in `[0, m)` when `0 < m`. -/
def modularRoute (out : Form n) (m : ℕ) (rows : List (Fin n → ℤ)) (init : ℤ) : ℤ :=
  (((rows.map fun row => AffineSummary.map (Int.castRingHom (ZMod m)) (out.summary row)).prod.act
    (init : ZMod m)).val : ℤ)

/-- **Residue of the modular fold.** Reduction to `ZMod m` carries the modular
fold of an admitted body to the ordered product of the reduced summaries, for
every stream, the empty one included. -/
theorem cast_foldall_modStep {body : Expr n} {out : Form n} (h : compile body = some out)
    (m : ℕ) (rows : List (Fin n → ℤ)) (init : ℤ) :
    ((foldall (modStep body m) rows init : ℤ) : ZMod m) =
      (rows.map fun row => AffineSummary.map (Int.castRingHom (ZMod m)) (out.summary row)).prod.act
        (init : ZMod m) := by
  rw [(ZMod.intCast_eq_intCast_iff _ _ m).mpr
    (foldall_modStep_modEq body m rows (Int.ModEq.refl init)), sourceFold_eq_prod h]
  exact (AffineSummary.act_prod_map (Int.castRingHom (ZMod m)) out.summary rows init).symm

/-- **Modular affine fold.** For a positive modulus and a nonempty stream, the
source fold of an admitted body `(% e m)` equals the modular route. -/
theorem foldall_modStep_eq_modularRoute {body : Expr n} {out : Form n}
    (h : compile body = some out) (m : ℕ) [NeZero m] {rows : List (Fin n → ℤ)}
    (hrows : rows ≠ []) (init : ℤ) :
    foldall (modStep body m) rows init = modularRoute out m rows init := by
  rw [modularRoute, ← cast_foldall_modStep h, ZMod.val_intCast,
    foldall_modStep_of_ne_nil body _ hrows, Int.fmod_eq_emod_of_nonneg _ (Int.natCast_nonneg m),
    Int.emod_emod]

/-- The main theorem with Lean's `%` in the step. -/
theorem foldl_emod_eq_modularRoute {body : Expr n} {out : Form n} (h : compile body = some out)
    (m : ℕ) [NeZero m] {rows : List (Fin n → ℤ)} (hrows : rows ≠ []) (init : ℤ) :
    rows.foldl (fun state row => body.eval row state % (m : ℤ)) init =
      modularRoute out m rows init := by
  rw [← foldall_modStep_eq_modularRoute h m hrows init]
  simp only [foldall, modStep_of_nonneg body (Int.natCast_nonneg m)]

/-- The modular fold, piecewise. The empty stream returns the initial
accumulator unreduced. -/
theorem foldall_modStep_eq {body : Expr n} {out : Form n} (h : compile body = some out)
    (m : ℕ) [NeZero m] (rows : List (Fin n → ℤ)) (init : ℤ) :
    foldall (modStep body m) rows init =
      if rows = [] then init else modularRoute out m rows init := by
  split_ifs with hrows
  · subst hrows
    rfl
  · exact foldall_modStep_eq_modularRoute h m hrows init

/-- **Prefix scan.** Every accumulator after at least one step is the route of
the corresponding prefix. -/
theorem getElem_trajectory_modStep {body : Expr n} {out : Form n} (h : compile body = some out)
    (m : ℕ) [NeZero m] (rows : List (Fin n → ℤ)) (init : ℤ) {i : ℕ}
    (hi : i < (trajectory (modStep body m) rows init).length) (hi0 : 0 < i) :
    (trajectory (modStep body m) rows init)[i] = modularRoute out m (rows.take i) init := by
  have hlen : i < rows.length + 1 := by simpa [trajectory] using hi
  have hne : rows.take i ≠ [] := by
    rw [ne_eq, List.take_eq_nil_iff, not_or]
    refine ⟨Nat.pos_iff_ne_zero.mp hi0, fun hr => ?_⟩
    subst hr
    simp at hlen
    omega
  simp only [trajectory, List.getElem_scanl]
  exact foldall_modStep_eq_modularRoute h m hne init

/-- **Constant stretch.** `k ≥ 1` copies of one row act as the `k`-th power of
its reduced summary. -/
theorem foldall_modStep_replicate {body : Expr n} {out : Form n} (h : compile body = some out)
    (m : ℕ) [NeZero m] {k : ℕ} (hk : k ≠ 0) (row : Fin n → ℤ) (init : ℤ) :
    foldall (modStep body m) (List.replicate k row) init =
      (((AffineSummary.map (Int.castRingHom (ZMod m)) (out.summary row) ^ k).act
        (init : ZMod m)).val : ℤ) := by
  rw [foldall_modStep_eq_modularRoute h m (mt (List.replicate_eq_nil_iff row).mp hk),
    modularRoute, List.map_replicate, List.prod_replicate]

/-- The constant stretch in closed form: a geometric sum in `ZMod m`. -/
theorem foldall_modStep_replicate_closed {body : Expr n} {out : Form n}
    (h : compile body = some out) (m : ℕ) [NeZero m] {k : ℕ} (hk : k ≠ 0)
    (row : Fin n → ℤ) (init : ℤ) :
    foldall (modStep body m) (List.replicate k row) init =
      (((out.scale.eval row : ZMod m) ^ k * (init : ZMod m) +
        (∑ i ∈ Finset.range k, (out.scale.eval row : ZMod m) ^ i) *
          (out.offset.eval row : ZMod m)).val : ℤ) := by
  rw [foldall_modStep_replicate h m hk, AffineSummary.act_pow]
  rfl

/-- The reduced summary of a row depends only on the residues of its inputs. -/
theorem map_summary_congr (out : Form n) (m : ℕ) {row row' : Fin n → ℤ}
    (hrow : ∀ i, row i ≡ row' i [ZMOD m]) :
    AffineSummary.map (Int.castRingHom (ZMod m)) (out.summary row) =
      AffineSummary.map (Int.castRingHom (ZMod m)) (out.summary row') :=
  AffineSummary.ext ((ZMod.intCast_eq_intCast_iff _ _ m).mpr (out.scale.eval_modEq hrow))
    ((ZMod.intCast_eq_intCast_iff _ _ m).mpr (out.offset.eval_modEq hrow))

/-- The route depends only on the residues of the inputs and of the initial
accumulator: execution may reduce them before evaluating coefficients. -/
theorem modularRoute_reduce_inputs (out : Form n) (m : ℕ) (rows : List (Fin n → ℤ))
    (init : ℤ) :
    modularRoute out m (rows.map fun row i => row i % (m : ℤ)) (init % (m : ℤ)) =
      modularRoute out m rows init := by
  simp only [modularRoute, List.map_map, ZMod.intCast_mod]
  congr 4
  exact List.map_congr_left fun row _ =>
    map_summary_congr out m fun i => Int.mod_modEq (row i) m

/-! ## Controls -/

/-- `10 * acc + item`: one decimal digit per answer. -/
def tenAccPlusItem : Expr 1 := .bin .add (.bin .mul (.lit 10) .acc) (.input 0)

/-- The compiled form of `10 * acc + item`. -/
def tenAccPlusItemForm : Form 1 :=
  .affine (.bin .add (.bin .mul (.lit 10) (.lit 1)) (.lit 0))
    (.bin .add (.bin .mul (.lit 10) (.lit 0)) (.input 0))

theorem compile_tenAccPlusItem : compile tenAccPlusItem = some tenAccPlusItemForm := rfl

/-- `(% (+ (* 10 acc) item) 7)` over the digits `1, 2, 3` from `0` computes
`123 mod 7 = 4`: stepwise, by one reduction at the end, and by the route. -/
theorem decimal_residue :
    foldall (modStep tenAccPlusItem 7) [![1], ![2], ![3]] 0 = 4 ∧
      sourceFold tenAccPlusItem [![1], ![2], ![3]] 0 = 123 ∧
      modularRoute tenAccPlusItemForm 7 [![1], ![2], ![3]] 0 = 4 := by
  decide

/-- `acc + item`. -/
def accPlusItem : Expr 1 := .bin .add .acc (.input 0)

/-- The compiled form of `acc + item`. -/
def accPlusItemForm : Form 1 := .affine (.bin .add (.lit 1) (.lit 0)) (.bin .add (.lit 0) (.input 0))

theorem compile_accPlusItem : compile accPlusItem = some accPlusItemForm := rfl

/-- The nonempty hypothesis cannot be dropped. On the empty stream the fold
returns `init = -5` unreduced, while the route returns the residue `1`. -/
theorem empty_stream_unreduced :
    foldall (modStep accPlusItem 3) [] (-5) = -5 ∧ modularRoute accPlusItemForm 3 [] (-5) = 1 := by
  decide

/-- The compiled form of `acc`. -/
def accForm : Form 1 := .affine (.lit 1) (.lit 0)

theorem compile_acc : compile (.acc : Expr 1) = some accForm := rfl

/-- `(% acc item)`: the dividend `acc` is admitted, but the divisor is the item. -/
def accModItem (row : Fin 1 → ℤ) (acc : ℤ) : ℤ := Int.fmod acc (row 0)

/-- The modulus must be a literal. From `7`, one step of `(% acc item)` gives
`1` with item `3` and `2` with item `5`. The route of the dividend `acc` for a
fixed `m` gives one value on both streams, so no fixed modulus reproduces the
fold. -/
theorem item_modulus_has_no_fixed_ring :
    ¬ ∃ m : ℕ, foldall accModItem [![3]] 7 = modularRoute accForm m [![3]] 7 ∧
      foldall accModItem [![5]] 7 = modularRoute accForm m [![5]] 7 := by
  rintro ⟨m, h3, h5⟩
  have e3 : foldall accModItem [![3]] 7 = 1 := by decide
  have e5 : foldall accModItem [![5]] 7 = 2 := by decide
  have hr : modularRoute accForm m [![3]] 7 = modularRoute accForm m [![5]] 7 := rfl
  omega

/-- A negative literal modulus is outside the route. PeTTa's `%` takes the
sign of the divisor, so one step of `(% (+ acc item) -3)` from `0` with item
`1` gives `-2`, while residues modulo `3` lie in `[0, 3)`. The
reduce-at-the-end law `foldall_modStep_of_ne_nil` still applies. -/
theorem negative_modulus_outside_route :
    foldall (modStep accPlusItem (-3)) [![1]] 0 = -2 ∧
      modularRoute accPlusItemForm 3 [![1]] 0 = 1 := by
  decide

/-- `acc - 5`, with no inputs. -/
def accMinusFive : Expr 0 := .bin .sub .acc (.lit 5)

/-- The compiled form of `acc - 5`. -/
def accMinusFiveForm : Form 0 := .affine (.bin .sub (.lit 1) (.lit 0)) (.bin .sub (.lit 0) (.lit 5))

theorem compile_accMinusFive : compile accMinusFive = some accMinusFiveForm := rfl

/-- The route is specific to floor modulo. HE and Prime `%` is the truncating
remainder `Int.tmod`, whose sign follows the dividend. One step of
`(% (- acc 5) 3)` from `0` gives `-2` there, but `1` under PeTTa's `%` and by
the route. -/
theorem truncated_remainder_outside_route :
    foldall (fun row acc => Int.tmod (accMinusFive.eval row acc) 3) [![]] 0 = -2 ∧
      foldall (modStep accMinusFive 3) [![]] 0 = 1 ∧
      modularRoute accMinusFiveForm 3 [![]] 0 = 1 := by
  decide

end Mettapedia.GSLT.Dynamics.ModularAffineFold
