import Mettapedia.Algebra.AffineSummary
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A scoped integer expression language and its affine compiler

The source language has exact integer literals, finitely scoped inputs, an
accumulator, addition, subtraction and multiplication. Coefficient expressions
cannot mention the accumulator. The compiler is executable and conservative:
it declines a multiplication when both operands depend on the accumulator.

Admission is a syntactic fragment with a semantic correctness theorem, not a
decision procedure for every semantically affine program. In particular it
does not discover cancellation of nonlinear subexpressions. Runtime effects,
operator lookup, type promotion, and resource accounting are outside this
pure source language and must be checked by its frontend.
-/

namespace Mettapedia.GSLT.AffineExpression

open Mettapedia.Algebra

/-- Binary operations of the exact integer source language. -/
inductive Op where
  | add | sub | mul
  deriving DecidableEq, Repr

def Op.eval : Op → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Input scope is a finite coordinate set; accumulator access is explicit. -/
inductive Expr (n : Nat) where
  | lit : Int → Expr n
  | input : Fin n → Expr n
  | acc : Expr n
  | bin : Op → Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

def Expr.eval (env : Fin n → Int) (state : Int) : Expr n → Int
  | .lit k => k
  | .input i => env i
  | .acc => state
  | .bin op l r => op.eval (l.eval env state) (r.eval env state)

/-- Accumulator-free coefficient syntax. It may depend on any input slot. -/
inductive Coeff (n : Nat) where
  | lit : Int → Coeff n
  | input : Fin n → Coeff n
  | bin : Op → Coeff n → Coeff n → Coeff n
  deriving DecidableEq, Repr

def Coeff.eval (env : Fin n → Int) : Coeff n → Int
  | .lit k => k
  | .input i => env i
  | .bin op l r => op.eval (l.eval env) (r.eval env)

/-- Constants are retained distinctly so multiplication admission needs no
semantic equality oracle for coefficient expressions. -/
inductive Form (n : Nat) where
  | constant : Coeff n → Form n
  | affine : Coeff n → Coeff n → Form n
  deriving DecidableEq, Repr

def Form.scale : Form n → Coeff n
  | .constant _ => .lit 0
  | .affine a _ => a

def Form.offset : Form n → Coeff n
  | .constant b => b
  | .affine _ b => b

def Form.summary (env : Fin n → Int) (f : Form n) : AffineSummary Int :=
  ⟨f.scale.eval env, f.offset.eval env⟩

def Form.apply (env : Fin n → Int) (state : Int) (f : Form n) : Int :=
  (f.summary env).act state

/-- Compile a source operation. Products retain source argument order. -/
def combine : Op → Form n → Form n → Option (Form n)
  | op, .constant l, .constant r => some (.constant (.bin op l r))
  | .add, l, r => some (.affine (.bin .add l.scale r.scale)
      (.bin .add l.offset r.offset))
  | .sub, l, r => some (.affine (.bin .sub l.scale r.scale)
      (.bin .sub l.offset r.offset))
  | .mul, .constant c, .affine a b =>
      some (.affine (.bin .mul c a) (.bin .mul c b))
  | .mul, .affine a b, .constant c =>
      some (.affine (.bin .mul a c) (.bin .mul b c))
  | .mul, .affine _ _, .affine _ _ => none

def compile : Expr n → Option (Form n)
  | .lit k => some (.constant (.lit k))
  | .input i => some (.constant (.input i))
  | .acc => some (.affine (.lit 1) (.lit 0))
  | .bin op l r => do combine op (← compile l) (← compile r)

theorem combine_sound (op : Op) (l r out : Form n)
    (h : combine op l r = some out) (env : Fin n → Int) (state : Int) :
    out.apply env state = op.eval (l.apply env state) (r.apply env state) := by
  cases op <;> cases l <;> cases r <;>
    simp [combine] at h <;> subst out <;>
    simp [Form.apply, Form.summary, Form.scale, Form.offset,
      Coeff.eval, Op.eval, AffineSummary.act] <;> ring

/-- Soundness compares an independently defined recursive source evaluator
with the compiled pair of coefficient expressions. -/
theorem compile_sound (expr : Expr n) (out : Form n)
    (h : compile expr = some out) (env : Fin n → Int) (state : Int) :
    out.apply env state = expr.eval env state := by
  induction expr generalizing out with
  | lit k =>
      simp [compile] at h
      subst out
      simp [Form.apply, Form.summary, Form.scale, Form.offset,
        Coeff.eval, AffineSummary.act, Expr.eval]
  | input i =>
      simp [compile] at h
      subst out
      simp [Form.apply, Form.summary, Form.scale, Form.offset,
        Coeff.eval, AffineSummary.act, Expr.eval]
  | acc =>
      simp [compile] at h
      subst out
      simp [Form.apply, Form.summary, Form.scale, Form.offset,
        Coeff.eval, AffineSummary.act, Expr.eval]
  | bin op l r ihl ihr =>
      cases hl : compile l with
      | none => simp [compile, hl] at h
      | some lf =>
          cases hr : compile r with
          | none => simp [compile, hl, hr] at h
          | some rf =>
              have hc : combine op lf rf = some out := by
                simpa [compile, hl, hr] using h
              rw [combine_sound op lf rf out hc, ihl lf hl, ihr rf hr]
              rfl

/-- A source fold executes the expression afresh for each ordered input row. -/
def sourceFold (body : Expr n) (rows : List (Fin n → Int)) (initial : Int) : Int :=
  rows.foldl (fun state row => body.eval row state) initial

/-- A compiled fold executes coefficient expressions without rediscovering
accumulator dependence at each row. -/
def compiledFold (body : Form n) (rows : List (Fin n → Int)) (initial : Int) : Int :=
  rows.foldl (fun state row => body.apply row state) initial

theorem compiledFold_correct (body : Expr n) (out : Form n)
    (h : compile body = some out) (rows : List (Fin n → Int)) (initial : Int) :
    compiledFold out rows initial = sourceFold body rows initial := by
  unfold compiledFold sourceFold
  congr 1
  funext state row
  exact compile_sound body out h row state

/-- Ordered matrix composition and sequential source evaluation agree for
every accepted body, every input stream, and every initial accumulator. -/
theorem summary_correct (body : Expr n) (out : Form n)
    (h : compile body = some out) (rows : List (Fin n → Int)) (initial : Int) :
    (rows.map out.summary).prod.act initial = sourceFold body rows initial := by
  rw [← AffineSummary.run_eq_summary]
  simpa [AffineSummary.run, List.foldl_map, compiledFold, Form.apply] using
    compiledFold_correct body out h rows initial

/-- A prefix can be consumed once and its accumulator transferred to the
remaining suffix; the consumed prefix is never replayed. -/
theorem resume_correct (body : Expr n) (out : Form n)
    (h : compile body = some out) (before after : List (Fin n → Int)) (initial : Int) :
    compiledFold out after (sourceFold body before initial) =
      sourceFold body (before ++ after) initial := by
  rw [compiledFold_correct body out h]
  simp [sourceFold, List.foldl_append]

/-- Syntactic polynomial degree in the accumulator. This is an upper bound
on semantic degree because the syntax has not undergone cancellation. -/
def Op.degree : Op → Nat → Nat → Nat
  | .add | .sub => max
  | .mul => (· + ·)

def Expr.degree : Expr n → Nat
  | .lit _ | .input _ => 0
  | .acc => 1
  | .bin op l r => op.degree l.degree r.degree

def Form.degree : Form n → Nat
  | .constant _ => 0
  | .affine _ _ => 1

theorem combine_degree (op : Op) (l r out : Form n)
    (h : combine op l r = some out) : out.degree = op.degree l.degree r.degree := by
  cases op <;> cases l <;> cases r <;>
    simp [combine] at h <;> subst out <;> rfl

theorem combine_exists_iff (op : Op) (l r : Form n) :
    (∃ out, combine op l r = some out) ↔ op.degree l.degree r.degree ≤ 1 := by
  cases op <;> cases l <;> cases r <;> simp [combine, Op.degree, Form.degree]

theorem compile_degree (e : Expr n) (out : Form n) (h : compile e = some out) :
    out.degree = e.degree := by
  induction e generalizing out with
  | lit | input | acc => simp [compile] at h; subst out; rfl
  | bin op l r ihl ihr =>
      cases hl : compile l with
      | none => simp [compile, hl] at h
      | some lf =>
          cases hr : compile r with
          | none => simp [compile, hl, hr] at h
          | some rf =>
              have hc : combine op lf rf = some out := by
                simpa [compile, hl, hr] using h
              rw [combine_degree op lf rf out hc, ihl lf hl, ihr rf hr]
              rfl

/-- The recognizer is complete for the explicitly defined degree-at-most-one
grammar. It does not claim maximality among semantic integer programs. -/
theorem compile_exists_iff (e : Expr n) :
    (∃ out, compile e = some out) ↔ e.degree ≤ 1 := by
  constructor
  · rintro ⟨out, h⟩
    rw [← compile_degree e out h]
    cases out <;> simp [Form.degree]
  · induction e with
    | lit k => exact fun _ => ⟨_, rfl⟩
    | input i => exact fun _ => ⟨_, rfl⟩
    | acc => exact fun _ => ⟨_, rfl⟩
    | bin op l r ihl ihr =>
        intro h
        have bounds : l.degree ≤ 1 ∧ r.degree ≤ 1 := by
          cases op <;> simp only [Expr.degree, Op.degree] at h <;> omega
        obtain ⟨lf, hl⟩ := ihl bounds.1
        obtain ⟨rf, hr⟩ := ihr bounds.2
        have combined : op.degree lf.degree rf.degree ≤ 1 := by
          rw [compile_degree l lf hl, compile_degree r rf hr]
          exact h
        obtain ⟨out, ho⟩ := (combine_exists_iff op lf rf).mpr combined
        exact ⟨out, by simp [compile, hl, hr, ho]⟩

end Mettapedia.GSLT.AffineExpression
