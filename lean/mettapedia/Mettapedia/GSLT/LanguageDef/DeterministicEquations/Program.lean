import Mathlib.Data.List.Basic

/-!
# Deterministic equation programs and their evaluator

A deterministic equation program is a list of equations `f p₁ … pₙ = r`
between first-order terms: the left side is a call of a symbol `f` whose
arguments are patterns, and the right side is a term over the variables of
the left side and of enclosing `let`s.  The evaluator is call by value and
reads a term as follows.

* A variable denotes its binding; an unbound variable fails.  A symbol, a
  literal atom and the empty expression denote themselves.
* `(let x e b)` with a variable `x` evaluates `e`, binds `x` to its value and
  evaluates `b`; any other `let` of that shape fails.
* `(metta-nullary s)` with a symbol `s` denotes the expression `(s)`.
* Any other expression evaluates its elements from left to right.  When its
  head is a symbol `f`: if some equation defines `f` at the call's arity, the
  first equation whose left side matches the evaluated call gives its right
  side, evaluated under the match, and a call no equation matches fails; a
  symbol defined only at other arities fails; otherwise the host's primitive
  for `f` gives the value or fails, and a symbol the host does not handle is
  a constructor.  An expression whose head is not a symbol, and a list value,
  is a constructor of its evaluated elements.

Every evaluation step spends fuel, and running out of fuel is its own
outcome, distinct from failure.  Fuel is monotone: an evaluation that ends
with some fuel ends the same way with more (`eval_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- First-order terms: symbols, other atoms (numbers, strings) by their
spelling, variables, expressions, and list values. -/
inductive Term where
  | sym (name : String)
  | lit (spelling : String)
  | var (name : String)
  | expr (items : List Term)
  | list (items : List Term)
  deriving Repr, Inhabited

/-- Bindings of variables to values, the newest first. -/
abbrev Env := List (String × Term)

/-- The value a variable is bound to. -/
def Env.lookup (env : Env) (x : String) : Option Term :=
  (List.find? (fun b => b.1 == x) env).map (·.2)

mutual

/-- First-order matching of a pattern against a value: a variable binds the
value, an atom matches itself, and an expression or a list matches one of the
same kind and length element by element. -/
def matchTerm : Term → Term → Option Env
  | .var x, v => some [(x, v)]
  | .sym a, .sym b => if a = b then some [] else none
  | .lit a, .lit b => if a = b then some [] else none
  | .expr ps, .expr vs => matchTerms ps vs
  | .list ps, .list vs => matchTerms ps vs
  | _, _ => none

/-- Matching of a list of patterns against a list of values of its length. -/
def matchTerms : List Term → List Term → Option Env
  | [], [] => some []
  | p :: ps, v :: vs =>
    match matchTerm p v, matchTerms ps vs with
    | some e₁, some e₂ => some (e₁ ++ e₂)
    | _, _ => none
  | _, _ => none

end

/-- An equation `head params = body`, named. -/
structure Equation where
  name : String
  head : String
  params : List Term
  body : Term

/-- A program: its equations in execution order. -/
abbrev Program := List Equation

/-- Some equation defines `f` at arity `n`. -/
def Program.definesAt (P : Program) (f : String) (n : Nat) : Bool :=
  P.any (fun e => e.head == f && e.params.length == n)

/-- Some equation defines `f`. -/
def Program.defines (P : Program) (f : String) : Bool :=
  P.any (fun e => e.head == f)

/-- The first equation of `f` whose left side matches the values, with the
match. -/
def Program.select (P : Program) (f : String) (vs : List Term) :
    Option (Equation × Env) :=
  P.findSome? (fun e =>
    if e.head = f ∧ e.params.length = vs.length then
      (matchTerms e.params vs).map (fun σ => (e, σ))
    else none)

/-- What a host primitive does with a call: it does not handle it, fails, or
gives a value. -/
inductive PrimitiveResult where
  | unhandled
  | fault
  | value (v : Term)

/-- The host: its primitives, by head symbol and evaluated arguments. -/
structure Host where
  primitive : String → List Term → PrimitiveResult

/-- The outcome of an evaluation. -/
inductive Outcome where
  | value (v : Term)
  | failure
  | exhausted

/-- The outcome of evaluating a list of terms: their values, or the first
outcome that is not a value. -/
inductive ItemsOutcome where
  | values (vs : List Term)
  | stop (o : Outcome)

/-- The evaluation of the elements of an expression from left to right, with
a given evaluation of terms. -/
def evalItemsWith (ev : Env → Term → Outcome) (env : Env) : List Term → ItemsOutcome
  | [] => .values []
  | t :: ts =>
    match ev env t with
    | .value v =>
      match evalItemsWith ev env ts with
      | .values vs => .values (v :: vs)
      | .stop o => .stop o
    | o => .stop o

/-- A call of a symbol on evaluated arguments, with a given evaluation of the
selected equation's right side. -/
def applyWith (P : Program) (H : Host) (ev : Env → Term → Outcome) (f : String)
    (vs : List Term) : Outcome :=
  if P.definesAt f vs.length then
    match P.select f vs with
    | some (e, σ) => ev σ e.body
    | none => .failure
  else if P.defines f then .failure
  else
    match H.primitive f vs with
    | .fault => .failure
    | .value v => .value v
    | .unhandled => .value (.expr (.sym f :: vs))

/-- One step of the evaluation of a term, with a given evaluation of its
subterms and of its calls. -/
def evalStep (ev : Env → Term → Outcome) (call : String → List Term → Outcome)
    (env : Env) : Term → Outcome
  | .var x =>
    match env.lookup x with
    | some v => .value v
    | none => .failure
  | .sym s => .value (.sym s)
  | .lit s => .value (.lit s)
  | .list items =>
    match evalItemsWith ev env items with
    | .values vs => .value (.list vs)
    | .stop o => o
  | .expr [] => .value (.expr [])
  | .expr [.sym "let", .var x, e, b] =>
    match ev env e with
    | .value v => ev ((x, v) :: env) b
    | o => o
  | .expr [.sym "let", _, _, _] => .failure
  | .expr [.sym "metta-nullary", .sym s] => .value (.expr [.sym s])
  | .expr [.sym "metta-nullary", _] => .failure
  | .expr (.sym f :: args) =>
    match evalItemsWith ev env args with
    | .values vs => call f vs
    | .stop o => o
  | .expr items =>
    match evalItemsWith ev env items with
    | .values vs => .value (.expr vs)
    | .stop o => o

/-- Evaluation of a term under an environment with some fuel: each step
spends one unit, the evaluation of the selected equation's right side
included. -/
def eval (P : Program) (H : Host) : Nat → Env → Term → Outcome
  | 0, _, _ => .exhausted
  | n + 1, env, t => evalStep (eval P H n) (applyWith P H (eval P H n)) env t

/-- The evaluation of a list of terms with some fuel. -/
abbrev evalItems (P : Program) (H : Host) (n : Nat) (env : Env) (ts : List Term) :
    ItemsOutcome :=
  evalItemsWith (eval P H n) env ts

/-- A call with some fuel. -/
abbrev apply (P : Program) (H : Host) (n : Nat) (f : String) (vs : List Term) :
    Outcome :=
  applyWith P H (eval P H n) f vs

/-! ## Fuel -/

/-- An outcome refines another when the other ran out of fuel or they are
equal. -/
def Refines (o o' : Outcome) : Prop := o = .exhausted ∨ o = o'

theorem Refines.refl (o : Outcome) : Refines o o := Or.inr rfl

theorem Refines.eq {o o' : Outcome} (h : Refines o o') (ho : o ≠ .exhausted) :
    o = o' := h.resolve_left ho

theorem evalItemsWith_refines {ev ev' : Env → Term → Outcome}
    (h : ∀ env t, Refines (ev env t) (ev' env t)) (env : Env) :
    ∀ ts, evalItemsWith ev env ts = evalItemsWith ev' env ts ∨
      evalItemsWith ev env ts = .stop .exhausted
  | [] => Or.inl rfl
  | t :: ts => by
    simp only [evalItemsWith]
    rcases h env t with ht | ht
    · rw [ht]
      exact Or.inr rfl
    · rw [← ht]
      split
      · rcases evalItemsWith_refines h env ts with hs | hs
        · rw [hs]
          exact Or.inl rfl
        · rw [hs]
          exact Or.inr rfl
      · exact Or.inl rfl

theorem applyWith_refines (P : Program) (H : Host) {ev ev' : Env → Term → Outcome}
    (h : ∀ env t, Refines (ev env t) (ev' env t)) (f : String) (vs : List Term) :
    Refines (applyWith P H ev f vs) (applyWith P H ev' f vs) := by
  unfold applyWith
  split
  · split
    · exact h _ _
    · exact Refines.refl _
  · exact Refines.refl _

theorem evalStep_refines {ev ev' : Env → Term → Outcome}
    {call call' : String → List Term → Outcome}
    (h : ∀ env t, Refines (ev env t) (ev' env t))
    (hc : ∀ f vs, Refines (call f vs) (call' f vs)) (env : Env) (t : Term) :
    Refines (evalStep ev call env t) (evalStep ev' call' env t) := by
  unfold evalStep
  split
  · exact Refines.refl _
  · exact Refines.refl _
  · exact Refines.refl _
  · rename_i items
    rcases evalItemsWith_refines h env items with hs | hs
    · rw [hs]
      exact Refines.refl _
    · rw [hs]
      exact Or.inl rfl
  · exact Refines.refl _
  · rename_i x e b
    rcases h env e with he | he
    · rw [he]
      exact Or.inl rfl
    · rw [← he]
      split
      · exact h _ _
      · exact Refines.refl _
  · exact Refines.refl _
  · exact Refines.refl _
  · exact Refines.refl _
  · rename_i f args _ _ _ _
    rcases evalItemsWith_refines h env args with hs | hs
    · rw [hs]
      split
      · exact hc _ _
      · exact Refines.refl _
    · rw [hs]
      exact Or.inl rfl
  · rename_i items _ _ _ _ _ _
    rcases evalItemsWith_refines h env items with hs | hs
    · rw [hs]
      exact Refines.refl _
    · rw [hs]
      exact Or.inl rfl

/-- More fuel refines every evaluation. -/
theorem eval_refines_succ (P : Program) (H : Host) :
    ∀ n env t, Refines (eval P H n env t) (eval P H (n + 1) env t)
  | 0, _, _ => Or.inl rfl
  | n + 1, env, t => by
    simp only [eval]
    exact evalStep_refines (eval_refines_succ P H n)
      (applyWith_refines P H (eval_refines_succ P H n)) env t

/-- Fuel is monotone: an evaluation that ends with some fuel ends the same way
with more. -/
theorem eval_mono (P : Program) (H : Host) (n k : Nat) (env : Env) (t : Term)
    (h : eval P H n env t ≠ .exhausted) : eval P H (n + k) env t = eval P H n env t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have := (eval_refines_succ P H (n + k) env t).eq (by rw [ih]; exact h)
    rw [← Nat.add_assoc, ← this, ih]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
