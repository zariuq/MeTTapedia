import Mettapedia.GSLT.LanguageDef.AffineExpression
import Mettapedia.GSLT.Core.GSLT
import Lean.Elab.Tactic.Omega

/-!
# Operational semantics of affine-expression compilation

The source is an AST-level GSLT with eager, left-to-right integer reduction.
Its grammar admits nonlinear expressions as well: compiler rejection does not
mean source failure. Accepted compiled results coincide with *all* terminal
source results. This proves both preservation and absence of invented answers.

The exact source rewrite charge is retained independently of fused execution.
It is the charge of this DSL, not an assertion about another dialect's fuel.
There is no textual parser or native C realization in this module.
-/

namespace Mettapedia.GSLT.AffineExpression

inductive Step (env : Fin n → Int) (state : Int) : Expr n → Expr n → Prop where
  | input (i) : Step env state (.input i) (.lit (env i))
  | acc : Step env state .acc (.lit state)
  | calculate (op l r) : Step env state (.bin op (.lit l) (.lit r))
      (.lit (op.eval l r))
  | left {l l'} (op r) : Step env state l l' →
      Step env state (.bin op l r) (.bin op l' r)
  | right {r r'} (op l) : Step env state r r' →
      Step env state (.bin op (.lit l) r) (.bin op (.lit l) r')

def theory (env : Fin n → Int) (state : Int) : GSLT where
  Term := Expr n
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step env state
  rewrites_resp_left := by
    intro t t' u h step
    cases h
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step h
    cases h
    exact step

theorem step_preserves_eval {env : Fin n → Int} {state : Int} {e e' : Expr n}
    (h : Step env state e e') : e.eval env state = e'.eval env state := by
  induction h with
  | input | acc | calculate => rfl
  | left op r _ ih => simp [Expr.eval, ih]
  | right op l _ ih => simp [Expr.eval, ih]

private def appendPath {S : GSLT} {a b c : S.Term}
    (p : S.RewritePath a b) (q : S.RewritePath b c) : S.RewritePath a c :=
  match p with
  | .nil _ => q
  | .cons step rest => .cons step (appendPath rest q)

private def liftLeft {env : Fin n → Int} {state : Int} {l l' : Expr n}
    (op : Op) (r : Expr n) (path : (theory env state).RewritePath l l') :
    (theory env state).RewritePath (.bin op l r) (.bin op l' r) :=
  match path with
  | .nil _ => .nil _
  | .cons step rest => .cons (Step.left op r step) (liftLeft op r rest)

private def liftRight {env : Fin n → Int} {state : Int} {r r' : Expr n}
    (op : Op) (l : Int) (path : (theory env state).RewritePath r r') :
    (theory env state).RewritePath (.bin op (.lit l) r) (.bin op (.lit l) r') :=
  match path with
  | .nil _ => .nil _
  | .cons step rest => .cons (Step.right op l step) (liftRight op l rest)

/-- An actual source reduction path, generated recursively from syntax. -/
def normalize (env : Fin n → Int) (state : Int) (e : Expr n) :
    (theory env state).RewritePath e (.lit (e.eval env state)) :=
  match e with
  | .lit _ => .nil _
  | .input i => .cons (Step.input i) (.nil _)
  | .acc => .cons Step.acc (.nil _)
  | .bin op l r =>
      appendPath (liftLeft op r (normalize env state l))
        (appendPath (liftRight op (l.eval env state) (normalize env state r))
          (.cons (Step.calculate op _ _) (.nil _)))

theorem multistep_preserves_eval {env : Fin n → Int} {state : Int} {e e' : Expr n}
    (path : (theory env state).MultiStep e e') :
    e.eval env state = e'.eval env state :=
  match path with
  | .refl _ => rfl
  | .step h rest => (step_preserves_eval h).trans (multistep_preserves_eval rest)

private theorem forgetPath {S : GSLT} {a b : S.Term} (path : S.RewritePath a b) :
    S.MultiStep a b :=
  match path with
  | .nil _ => .refl _
  | .cons step rest => .step step (forgetPath rest)

theorem reaches_literal_iff (env : Fin n → Int) (state : Int) (e : Expr n) (v : Int) :
    (theory env state).MultiStep e (.lit v) ↔ e.eval env state = v := by
  constructor
  · exact multistep_preserves_eval
  · intro h
    rw [← h]
    exact forgetPath (normalize env state e)

theorem literal_normal (env : Fin n → Int) (state v : Int) :
    (theory env state).IsNormalForm (.lit v) := by
  rintro ⟨target, step⟩
  cases step

/-- Accepted compilation preserves and reflects observable terminal answers. -/
theorem compiled_reaches_iff (env : Fin n → Int) (state : Int)
    (e : Expr n) (f : Form n) (admitted : compile e = some f) (v : Int) :
    (theory env state).MultiStep e (.lit v) ↔ f.apply env state = v := by
  rw [reaches_literal_iff, compile_sound e f admitted]

/-- Pullback of any predicate on terminal integer observations. This is a
reachability-scale modal law; primitive source steps are not matrix steps. -/
theorem terminal_predicate_exact (env : Fin n → Int) (state : Int)
    (e : Expr n) (f : Form n) (admitted : compile e = some f) (P : Int → Prop) :
    (∃ v, (theory env state).MultiStep e (.lit v) ∧ P v) ↔ P (f.apply env state) := by
  simp only [compiled_reaches_iff env state e f admitted]
  constructor
  · rintro ⟨v, h, hp⟩
    simpa [h] using hp
  · intro hp
    exact ⟨_, rfl, hp⟩

/-- Exact primitive reduction count, computed without reading any values. -/
def Expr.work : Expr n → Nat
  | .lit _ => 0
  | .input _ | .acc => 1
  | .bin _ l r => l.work + r.work + 1

theorem step_work {env : Fin n → Int} {state : Int} {e e' : Expr n}
    (h : Step env state e e') : e.work = e'.work + 1 := by
  induction h with
  | input | acc | calculate => rfl
  | left op r _ ih => simp only [Expr.work] at *; omega
  | right op l _ ih => simp only [Expr.work] at *; omega

theorem path_work {env : Fin n → Int} {state : Int} {e e' : Expr n}
    (path : (theory env state).RewritePath e e') :
    e.work = path.length + e'.work :=
  match path with
  | .nil _ => by simp [GSLT.RewritePath.length]
  | .cons step rest => by
      have h := step_work step
      have ih := path_work rest
      simp only [GSLT.RewritePath.length]
      omega

theorem normalization_charge (env : Fin n → Int) (state : Int) (e : Expr n) :
    (normalize env state e).length = e.work := by
  have h := path_work (normalize env state e)
  simpa [Expr.work] using h.symm

end Mettapedia.GSLT.AffineExpression
