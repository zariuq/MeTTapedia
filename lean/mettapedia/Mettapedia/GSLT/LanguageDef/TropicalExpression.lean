import Mettapedia.Algebra.TropicalAffineSummary
import Mathlib.Data.ENat.Basic

/-!
# A scoped integer expression language and its tropical compiler

The source language has exact integer literals, finitely scoped inputs, an accumulator, and the
binary operations `+`, `-`, `min` and `max`. The compiler is parametrized by an `Extremum`, the
tropical addition it admits on the accumulator: `min` (min-plus) or `max` (max-plus).
`compile e` recognizes the bodies that denote `acc ↦ c` or `acc ↦ e (acc + a) b`, where the
coefficients `a`, `b` and `c` are accumulator-free coefficient syntax and a missing `b` means no
cap. The rules are:

* `acc` is the shift by `0` with no cap; a literal or an input is a constant;
* adding an accumulator-free term, on either side, or subtracting one on the right, moves the
  shift and the cap together;
* `e` of two compiled forms is their pointwise tropical sum. Shifts combine by `e` as well, since
  `e (acc + a) (acc + a') = acc + e a a'`. `min (acc + 1) (acc + 2)` is therefore admitted, as
  `acc + min 1 2`;
* the other extremum is compiled only between accumulator-free operands; a sum of two
  accumulator-dependent terms and the subtraction of an accumulator-dependent term are refused.

`compile_sound` proves that every compiled form denotes its source body. `compile_exists_iff`
proves that admission is exactly `Expr.degree e ≤ 1`, the syntactic degree in the accumulator of
the body as a tropical polynomial over the semiring of `e`. Admission is a syntactic fragment
with a semantic correctness theorem. It does not decide semantic tropical affinity:
`min acc (max acc 3)` denotes `acc` and is refused.

`Form.summary e` sends a compiled form, at each input row, to an affine summary over the
min-plus semiring `Tropical (WithTop ℤ)` (`Mettapedia.Algebra.TropicalAffineSummary`). For
`max` the accumulator enters negated: `x ↦ max (x + a) b` is `-x ↦ min (-x - a) (-b)`.
`summary_correct` proves that the ordered product of the row summaries, acting on the initial
accumulator, is the source fold.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.TropicalExpression

open Tropical Mettapedia.Algebra

/-- Binary operations of the exact integer source language. -/
inductive Op where
  | add | sub | min | max
  deriving DecidableEq, Repr

/-- Integer semantics of the operations. -/
def Op.eval : Op → ℤ → ℤ → ℤ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .min => fun x y => Min.min x y
  | .max => fun x y => Max.max x y

/-! ## The admitted extremum -/

/-- The tropical addition a compiler admits on the accumulator: `min` for the min-plus
semiring, `max` for the max-plus semiring. -/
inductive Extremum where
  | min | max
  deriving DecidableEq, Repr

namespace Extremum

/-- The source operation of an extremum. -/
def op : Extremum → Op
  | .min => .min
  | .max => .max

/-- The extremum on integers. -/
def eval (e : Extremum) : ℤ → ℤ → ℤ := e.op.eval

/-- The additive automorphism of `ℤ` carrying `e` to `min`: the identity for `min`, negation for
`max`. -/
def toMin : Extremum → ℤ ≃+ ℤ
  | .min => AddEquiv.refl ℤ
  | .max => AddEquiv.neg ℤ

theorem toMin_eval (e : Extremum) (x y : ℤ) :
    e.toMin (e.eval x y) = Min.min (e.toMin x) (e.toMin y) := by
  cases e <;> simp [toMin, eval, op, Op.eval]

/-- The accumulator as a min-plus state: `x ↦ trop (e.toMin x)`. -/
def toTropical (e : Extremum) (x : ℤ) : Tropical (WithTop ℤ) := trop ((e.toMin x : ℤ) : WithTop ℤ)

theorem toTropical_injective (e : Extremum) : Function.Injective e.toTropical :=
  fun _ _ h => e.toMin.injective (WithTop.coe_injective (trop_injective h))

/-- Shift by `a`, then cap by `b` under `e`; `b = none` is no cap. -/
def shiftCap (e : Extremum) (a : ℤ) (b : Option ℤ) (x : ℤ) : ℤ :=
  b.elim (x + a) (e.eval (x + a))

/-- The min-plus summary of `e.shiftCap a b`: the shift and the cap carried to `min`, with no
cap as `⊤`. -/
def shiftCapSummary (e : Extremum) (a : ℤ) (b : Option ℤ) :
    AffineSummary (Tropical (WithTop ℤ)) :=
  AffineSummary.minPlus (e.toMin a) (b.elim ⊤ fun b => ((e.toMin b : ℤ) : WithTop ℤ))

theorem act_shiftCapSummary (e : Extremum) (a : ℤ) (b : Option ℤ) (x : ℤ) :
    (e.shiftCapSummary a b).act (e.toTropical x) = e.toTropical (e.shiftCap a b x) := by
  cases b with
  | none =>
      rw [shiftCapSummary, toTropical, AffineSummary.act_minPlus_coe]
      simp [shiftCap, toTropical]
  | some b =>
      rw [shiftCapSummary, toTropical, AffineSummary.act_minPlus_coe]
      simp only [Option.elim, shiftCap, toTropical, toMin_eval, map_add, WithTop.coe_min]

end Extremum

/-! ## Source and compiled syntax -/

variable {n : ℕ}

/-- Input scope is a finite coordinate set; accumulator access is explicit. -/
inductive Expr (n : ℕ) where
  | lit : ℤ → Expr n
  | input : Fin n → Expr n
  | acc : Expr n
  | bin : Op → Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

def Expr.eval (env : Fin n → ℤ) (state : ℤ) : Expr n → ℤ
  | .lit k => k
  | .input i => env i
  | .acc => state
  | .bin op l r => op.eval (l.eval env state) (r.eval env state)

/-- Accumulator-free coefficient syntax. It may use every operation and every input slot. -/
inductive Coeff (n : ℕ) where
  | lit : ℤ → Coeff n
  | input : Fin n → Coeff n
  | bin : Op → Coeff n → Coeff n → Coeff n
  deriving DecidableEq, Repr

def Coeff.eval (env : Fin n → ℤ) : Coeff n → ℤ
  | .lit k => k
  | .input i => env i
  | .bin op l r => op.eval (l.eval env) (r.eval env)

/-- Compiled step forms. `const c` is `acc ↦ c`. `shift a b` is `acc ↦ acc + a`, capped by `b`
under the admitted extremum; `b = none` is no cap. -/
inductive Form (n : ℕ) where
  | const : Coeff n → Form n
  | shift : Coeff n → Option (Coeff n) → Form n
  deriving DecidableEq, Repr

/-- The step a compiled form denotes under the extremum `e`. -/
def Form.apply (e : Extremum) (env : Fin n → ℤ) (state : ℤ) : Form n → ℤ
  | .const c => c.eval env
  | .shift a b => e.shiftCap (a.eval env) (b.map (Coeff.eval env)) state

/-- The pointwise tropical sum of two forms under `e`. Shifts combine by `e`, since
`e (x + a) (x + a') = x + e a a'`, and caps combine by `e`, with no cap as the unit. -/
def Form.extremum (e : Extremum) : Form n → Form n → Form n
  | .const c, .const d => .const (.bin e.op c d)
  | .const c, .shift a b => .shift a (Option.merge (.bin e.op) (some c) b)
  | .shift a b, .const d => .shift a (Option.merge (.bin e.op) b (some d))
  | .shift a b, .shift a' b' => .shift (.bin e.op a a') (Option.merge (.bin e.op) b b')

/-- Compile a source operation. Accumulator-free operands of any operation give a constant.
Otherwise only a shift by an accumulator-free term and the admitted extremum are compiled. -/
def combine (e : Extremum) : Op → Form n → Form n → Option (Form n)
  | op, .const c, .const d => some (.const (.bin op c d))
  | .add, .shift a b, .const c => some (.shift (.bin .add a c) (b.map (.bin .add · c)))
  | .add, .const c, .shift a b => some (.shift (.bin .add c a) (b.map (.bin .add c ·)))
  | .sub, .shift a b, .const c => some (.shift (.bin .sub a c) (b.map (.bin .sub · c)))
  | op, l, r => if op = e.op then some (l.extremum e r) else none

/-- The tropical compiler for the admitted extremum `e`. -/
def compile (e : Extremum) : Expr n → Option (Form n)
  | .lit k => some (.const (.lit k))
  | .input i => some (.const (.input i))
  | .acc => some (.shift (.lit 0) none)
  | .bin op l r => do combine e op (← compile e l) (← compile e r)

/-! ## Soundness -/

theorem Form.apply_extremum (e : Extremum) (l r : Form n) (env : Fin n → ℤ) (state : ℤ) :
    (l.extremum e r).apply e env state = e.eval (l.apply e env state) (r.apply e env state) := by
  cases e <;> rcases l with c | ⟨a, _ | b⟩ <;> rcases r with d | ⟨a', _ | b'⟩ <;>
    simp [Form.extremum, Form.apply, Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval,
      Coeff.eval, Option.merge] <;> omega

theorem combine_sound (e : Extremum) (op : Op) (l r out : Form n)
    (h : combine e op l r = some out) (env : Fin n → ℤ) (state : ℤ) :
    out.apply e env state = op.eval (l.apply e env state) (r.apply e env state) := by
  cases e <;> cases op <;> rcases l with c | ⟨a, _ | b⟩ <;> rcases r with d | ⟨a', _ | b'⟩ <;>
    simp [combine, Extremum.op] at h <;> subst out <;>
    first
    | exact Form.apply_extremum _ _ _ env state
    | (simp [Form.apply, Extremum.shiftCap, Extremum.eval, Extremum.op, Op.eval, Coeff.eval] <;>
       omega)

/-- Soundness compares an independently defined recursive source evaluator with the compiled
form. -/
theorem compile_sound (e : Extremum) (expr : Expr n) (out : Form n)
    (h : compile e expr = some out) (env : Fin n → ℤ) (state : ℤ) :
    out.apply e env state = expr.eval env state := by
  induction expr generalizing out with
  | lit k =>
      simp only [compile, Option.some.injEq] at h
      subst out
      rfl
  | input i =>
      simp only [compile, Option.some.injEq] at h
      subst out
      rfl
  | acc =>
      simp only [compile, Option.some.injEq] at h
      subst out
      simp [Form.apply, Extremum.shiftCap, Coeff.eval, Expr.eval]
  | bin op l r ihl ihr =>
      cases hl : compile e l with
      | none => simp [compile, hl] at h
      | some lf =>
          cases hr : compile e r with
          | none => simp [compile, hl, hr] at h
          | some rf =>
              have hc : combine e op lf rf = some out := by
                simpa [compile, hl, hr] using h
              rw [combine_sound e op lf rf out hc, ihl lf hl, ihr rf hr]
              rfl

/-! ## The admission boundary -/

/-- The syntactic degree of a compiled operation, from the degrees of its operands: tropical
multiplication (`+`) adds degrees, the tropical sum (`e`) takes the larger one, subtraction of an
accumulator-free term keeps the degree. Every other combination with an accumulator-dependent
operand leaves the tropical polynomials of `e` and has degree `⊤`. -/
def Op.degree (e : Extremum) : Op → ℕ∞ → ℕ∞ → ℕ∞
  | .add, l, r => l + r
  | .sub, l, r => if r = 0 then l else ⊤
  | op, l, r => if op = e.op then Max.max l r else if l = 0 ∧ r = 0 then 0 else ⊤

/-- The syntactic degree of a body in the accumulator, as a polynomial over the tropical
semiring of `e`, or `⊤` outside those polynomials. No cancellation is detected. -/
def Expr.degree (e : Extremum) : Expr n → ℕ∞
  | .lit _ | .input _ => 0
  | .acc => 1
  | .bin op l r => op.degree e (l.degree e) (r.degree e)

/-- The degree of a compiled form: `0` for a constant, `1` for a shift-cap step. -/
def Form.degree : Form n → ℕ∞
  | .const _ => 0
  | .shift _ _ => 1

theorem combine_degree (e : Extremum) (op : Op) (l r out : Form n)
    (h : combine e op l r = some out) : out.degree = op.degree e l.degree r.degree := by
  cases e <;> cases op <;> rcases l with c | ⟨a, _ | b⟩ <;> rcases r with d | ⟨a', _ | b'⟩ <;>
    simp [combine, Extremum.op] at h <;> subst out <;>
    simp [Form.degree, Form.extremum, Op.degree, Extremum.op]

theorem combine_exists_iff (e : Extremum) (op : Op) (l r : Form n) :
    (∃ out, combine e op l r = some out) ↔ op.degree e l.degree r.degree ≤ 1 := by
  cases e <;> cases op <;> rcases l with c | ⟨a, _ | b⟩ <;> rcases r with d | ⟨a', _ | b'⟩ <;>
    simp [combine, Op.degree, Form.degree, Extremum.op] <;> decide

theorem compile_degree (e : Extremum) (expr : Expr n) (out : Form n)
    (h : compile e expr = some out) : out.degree = expr.degree e := by
  induction expr generalizing out with
  | lit | input | acc =>
      simp only [compile, Option.some.injEq] at h
      subst out
      rfl
  | bin op l r ihl ihr =>
      cases hl : compile e l with
      | none => simp [compile, hl] at h
      | some lf =>
          cases hr : compile e r with
          | none => simp [compile, hl, hr] at h
          | some rf =>
              have hc : combine e op lf rf = some out := by
                simpa [compile, hl, hr] using h
              rw [combine_degree e op lf rf out hc, ihl lf hl, ihr rf hr]
              rfl

/-- An operation of degree at most one has operands of degree at most one. -/
theorem Op.le_one_of_degree_le_one {e : Extremum} {op : Op} {l r : ℕ∞}
    (h : op.degree e l r ≤ 1) : l ≤ 1 ∧ r ≤ 1 := by
  cases op with
  | add => exact ⟨le_self_add.trans h, le_add_self.trans h⟩
  | sub =>
      simp only [Op.degree] at h
      split_ifs at h with hr
      · exact ⟨h, hr.le.trans zero_le_one⟩
      · simp at h
  | min | max =>
      simp only [Op.degree] at h
      split_ifs at h with he hz
      · exact max_le_iff.mp h
      · exact ⟨hz.1.le.trans zero_le_one, hz.2.le.trans zero_le_one⟩
      · simp at h

/-- The recognizer is complete for the explicitly defined degree-at-most-one grammar. It does not
claim maximality among semantically tropical-affine integer programs. -/
theorem compile_exists_iff (e : Extremum) (expr : Expr n) :
    (∃ out, compile e expr = some out) ↔ expr.degree e ≤ 1 := by
  constructor
  · rintro ⟨out, h⟩
    rw [← compile_degree e expr out h]
    cases out <;> simp [Form.degree]
  · induction expr with
    | lit k => exact fun _ => ⟨_, rfl⟩
    | input i => exact fun _ => ⟨_, rfl⟩
    | acc => exact fun _ => ⟨_, rfl⟩
    | bin op l r ihl ihr =>
        intro h
        have bounds := Op.le_one_of_degree_le_one (e := e) (op := op) h
        obtain ⟨lf, hl⟩ := ihl bounds.1
        obtain ⟨rf, hr⟩ := ihr bounds.2
        have combined : op.degree e lf.degree rf.degree ≤ 1 := by
          rw [compile_degree e l lf hl, compile_degree e r rf hr]
          exact h
        obtain ⟨out, ho⟩ := (combine_exists_iff e op lf rf).mpr combined
        exact ⟨out, by simp [compile, hl, hr, ho]⟩

/-! ## Constant coefficients -/

/-- The input-free value of coefficient syntax, if its syntax alone determines one. -/
def Coeff.const? : Coeff n → Option ℤ
  | .lit k => some k
  | .input _ => none
  | .bin op l r => l.const?.bind fun x => r.const?.map (op.eval x)

theorem Coeff.const?_sound {c : Coeff n} {k : ℤ} (h : c.const? = some k) (env : Fin n → ℤ) :
    c.eval env = k := by
  induction c generalizing k with
  | lit k' =>
      simp only [Coeff.const?, Option.some.injEq] at h
      exact h
  | input i => simp [Coeff.const?] at h
  | bin op l r ihl ihr =>
      simp only [Coeff.const?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      simp [Coeff.eval, ihl hx, ihr hy]

/-! ## Min-plus summaries and ordered folds -/

/-- The min-plus summary of a compiled form at one input row. -/
def Form.summary (e : Extremum) (env : Fin n → ℤ) : Form n → AffineSummary (Tropical (WithTop ℤ))
  | .const c => AffineSummary.constant (e.toTropical (c.eval env))
  | .shift a b => e.shiftCapSummary (a.eval env) (b.map (Coeff.eval env))

theorem Form.act_summary (e : Extremum) (f : Form n) (env : Fin n → ℤ) (state : ℤ) :
    (f.summary e env).act (e.toTropical state) = e.toTropical (f.apply e env state) := by
  cases f with
  | const c => exact AffineSummary.act_constant _ _
  | shift a b => exact e.act_shiftCapSummary _ _ state

/-- A source fold executes the body afresh for each ordered input row. -/
def sourceFold (body : Expr n) (rows : List (Fin n → ℤ)) (initial : ℤ) : ℤ :=
  rows.foldl (fun state row => body.eval row state) initial

/-- A compiled fold evaluates the compiled coefficients at each row. -/
def compiledFold (e : Extremum) (body : Form n) (rows : List (Fin n → ℤ)) (initial : ℤ) : ℤ :=
  rows.foldl (fun state row => body.apply e row state) initial

theorem compiledFold_correct (e : Extremum) (body : Expr n) (out : Form n)
    (h : compile e body = some out) (rows : List (Fin n → ℤ)) (initial : ℤ) :
    compiledFold e out rows initial = sourceFold body rows initial := by
  unfold compiledFold sourceFold
  congr 1
  funext state row
  exact compile_sound e body out h row state

/-- **Ordered summaries.** For every accepted body, the ordered product of the row summaries,
first row leftmost, acting on the initial accumulator is the source fold. -/
theorem summary_correct (e : Extremum) (body : Expr n) (out : Form n)
    (h : compile e body = some out) (rows : List (Fin n → ℤ)) (initial : ℤ) :
    (rows.map (out.summary e)).prod.act (e.toTropical initial) =
      e.toTropical (sourceFold body rows initial) := by
  rw [← AffineSummary.run_eq_summary, AffineSummary.run, List.foldl_map, sourceFold]
  exact List.foldl_hom e.toTropical fun state row => by
    rw [Form.act_summary, compile_sound e body out h]

end Mettapedia.GSLT.TropicalExpression
