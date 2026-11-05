import Mathlib.Tactic

/-!
# A query's body on the compiled tier: captures, and where per-path work runs

A query whose body is a control form runs on the compiled equation tier as
the body of an equation.  Two facts decide how.

**Captures.**  The body's variables that the surrounding evaluation has bound
hold values.  Where data and code share one syntax, a value can look like
code: an equation `(= (g $q) $q)` read from a space is data, but written into
a body's code it is a test, and the test evaluates.  The machine reads a bound
variable as its value (`evalEnv`).  Substituting the values into the code and
evaluating the result (`eval ∘ subst`) agrees with that reading exactly when
every value is inert, that is, left as it is by evaluation.  Compiling the
variables to parameter slots and running the code with the values as
arguments (`run ∘ compile`) agrees with it for every value.  The slots are
the positional entry of `Mettapedia.Machines.ParameterizedBodyEntry`, whose
`environments_refine` relates them to named environments; this file runs
them inside evaluation and sets them against substitution.

**Per-path work.**  A fan-out of `P` paths filtered to `A` answers: when the
machine interprets the continuation after each path, it takes
`(c + 1) * P + A` transitions for a continuation of `c` transitions; when the
whole body runs on the tier, the machine takes `A + 1` and the tier takes the
per-path steps.  Both answer the same list.

This file proves:
* `eval_subst_eq_evalEnv_iff`: substituting then evaluating agrees with the
  machine's reading on every body iff every value is inert;
* `subst_changes_answer`: an equation held as a value, substituted into the
  body `$v`, answers `False` where the machine answers the equation;
* `run_compile`, `run_compile_values`: code over parameter slots, run with
  the values as arguments, agrees with the machine's reading for every value;
* `interpreted_answers`, `onTier_answers`: both routes answer the filtered
  paths;
* `interpreted_steps`, `onTier_steps`: their machine transitions;
* `onTier_steps_le`: the tier route never takes more machine transitions,
  and `interpreted_unbounded`: with every path filtered out, the interpreted
  route's transitions grow with the paths while the tier route's stay one.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.QueryBodyOnTier

/-! ## Captures -/

/-- Terms whose data and code share one syntax: variables, symbols, and
`(= a b)`, which as code tests whether its sides' values are equal. -/
inductive Tm
  | var (x : Nat)
  | sym (s : Nat)
  | eq (a b : Tm)
  deriving DecidableEq

/-- The two answers of a test. -/
def tru : Tm := .sym 1
def fls : Tm := .sym 0

/-- The machine's reading of a body under an environment: a bound variable
reads as its value, which is not evaluated again. -/
def evalEnv (σ : Nat → Tm) : Tm → Tm
  | .var x => σ x
  | .sym s => .sym s
  | .eq a b => if evalEnv σ a = evalEnv σ b then tru else fls

/-- Evaluating code: a variable left in it stands for itself. -/
def eval : Tm → Tm
  | .var x => .var x
  | .sym s => .sym s
  | .eq a b => if eval a = eval b then tru else fls

/-- Substituting the environment's values into the code. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | .var x => σ x
  | .sym s => .sym s
  | .eq a b => .eq (subst σ a) (subst σ b)

/-- A value is inert when evaluating it leaves it as it is. -/
def Inert (v : Tm) : Prop := eval v = v

theorem eval_subst_of_inert (σ : Nat → Tm) (h : ∀ x, Inert (σ x)) (t : Tm) :
    eval (subst σ t) = evalEnv σ t := by
  induction t with
  | var x => exact h x
  | sym s => rfl
  | eq a b iha ihb => simp only [subst, eval, evalEnv, iha, ihb]

/-- Substitution into code is sound for every body exactly when every value
is inert: the body `$x` alone tells a value that is not. -/
theorem eval_subst_eq_evalEnv_iff (σ : Nat → Tm) :
    (∀ t, eval (subst σ t) = evalEnv σ t) ↔ ∀ x, Inert (σ x) := by
  constructor
  · intro h x
    exact h (.var x)
  · intro h t
    exact eval_subst_of_inert σ h t

/-- An equation held as data, as a space holds `(= (g $q) $q)`. -/
def heldEquation : Tm := .eq (.sym 5) (.var 9)

theorem heldEquation_not_inert : ¬ Inert heldEquation := by
  simp [Inert, heldEquation, eval, fls]

/-- The body `$v`, with `$v` bound to the held equation: the machine answers
the equation; the substituted code tests it and answers `False`. -/
theorem subst_changes_answer :
    evalEnv (fun _ => heldEquation) (.var 0) = heldEquation ∧
    eval (subst (fun _ => heldEquation) (.var 0)) = fls := by
  refine ⟨rfl, ?_⟩
  simp [subst, eval, heldEquation]

/-- Code over a body's parameters: a parameter is a slot. -/
inductive Code
  | slot (i : Nat)
  | free (x : Nat)
  | sym (s : Nat)
  | eq (a b : Code)

/-- Compiling a body over the parameters `ps`: a parameter becomes its slot,
any other variable stays free. -/
def compile (ps : List Nat) : Tm → Code
  | .var x => if x ∈ ps then .slot (ps.idxOf x) else .free x
  | .sym s => .sym s
  | .eq a b => .eq (compile ps a) (compile ps b)

/-- Running code with the arguments in its slots: a slot's argument is read
as a value, never evaluated. -/
def run (args : List Tm) : Code → Tm
  | .slot i => args.getD i (.sym 0)
  | .free x => .var x
  | .sym s => .sym s
  | .eq a b => if run args a = run args b then tru else fls

/-- The environment the parameters and the arguments make. -/
def bind (ps : List Nat) (args : List Tm) (x : Nat) : Tm :=
  if x ∈ ps then args.getD (ps.idxOf x) (.sym 0) else .var x

theorem run_compile (ps : List Nat) (args : List Tm) (t : Tm) :
    run args (compile ps t) = evalEnv (bind ps args) t := by
  induction t with
  | var x => by_cases hx : x ∈ ps <;> simp [compile, run, evalEnv, bind, hx]
  | sym s => rfl
  | eq a b iha ihb => simp only [compile, run, evalEnv, iha, ihb]

/-- With the environment's values of the parameters as arguments, the
compiled body answers as the machine reads it, whatever the values are. -/
theorem run_compile_values (σ : Nat → Tm) (ps : List Nat)
    (hfree : ∀ x, x ∉ ps → σ x = .var x) (t : Tm) :
    run (ps.map σ) (compile ps t) = evalEnv σ t := by
  have hbind : bind ps (ps.map σ) = σ := by
    funext x
    by_cases hx : x ∈ ps
    · have hlt : ps.idxOf x < ps.length := List.idxOf_lt_length_iff.mpr hx
      simp [bind, hx, hlt, List.getElem_idxOf]
    · simp [bind, hx, hfree x hx]
  rw [run_compile, hbind]

/-! ## Per-path work -/

variable {α β : Type}

/-- The machine interprets the continuation after each path: it receives the
path (one transition), runs the continuation (`c` transitions) and delivers
an answer (one transition).  Machine transitions, then answers. -/
def interpreted (c : Nat) (k : α → Option β) : List α → Nat × List β
  | [] => (0, [])
  | p :: ps =>
      match k p with
      | some b => ((interpreted c k ps).1 + (c + 2), b :: (interpreted c k ps).2)
      | none => ((interpreted c k ps).1 + (c + 1), (interpreted c k ps).2)

/-- The tier runs the paths and the continuation (`d` steps a path); the
machine delivers each answer (one transition).  Machine transitions, tier
steps, answers. -/
def tierRun (d : Nat) (k : α → Option β) : List α → Nat × Nat × List β
  | [] => (0, 0, [])
  | p :: ps =>
      match k p with
      | some b => ((tierRun d k ps).1 + 1, (tierRun d k ps).2.1 + d,
          b :: (tierRun d k ps).2.2)
      | none => ((tierRun d k ps).1, (tierRun d k ps).2.1 + d,
          (tierRun d k ps).2.2)

/-- The whole body on the tier: the machine offers it (one transition). -/
def onTier (d : Nat) (k : α → Option β) (ps : List α) : Nat × Nat × List β :=
  ((tierRun d k ps).1 + 1, (tierRun d k ps).2.1, (tierRun d k ps).2.2)

theorem interpreted_answers (c : Nat) (k : α → Option β) (ps : List α) :
    (interpreted c k ps).2 = ps.filterMap k := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases h : k p <;> simp [interpreted, h, ih]

theorem tierRun_spec (d : Nat) (k : α → Option β) (ps : List α) :
    (tierRun d k ps).1 = (ps.filterMap k).length ∧
    (tierRun d k ps).2.1 = d * ps.length ∧
    (tierRun d k ps).2.2 = ps.filterMap k := by
  induction ps with
  | nil => simp [tierRun]
  | cons p ps ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      cases h : k p <;> simp [tierRun, h, h1, h2, h3] <;> ring

theorem onTier_answers (d : Nat) (k : α → Option β) (ps : List α) :
    (onTier d k ps).2.2 = ps.filterMap k :=
  (tierRun_spec d k ps).2.2

theorem interpreted_steps (c : Nat) (k : α → Option β) (ps : List α) :
    (interpreted c k ps).1 = (c + 1) * ps.length + (ps.filterMap k).length := by
  induction ps with
  | nil => simp [interpreted]
  | cons p ps ih => cases h : k p <;> simp [interpreted, h, ih] <;> ring

theorem onTier_steps (d : Nat) (k : α → Option β) (ps : List α) :
    (onTier d k ps).1 = (ps.filterMap k).length + 1 ∧
    (onTier d k ps).2.1 = d * ps.length := by
  obtain ⟨h1, h2, _⟩ := tierRun_spec d k ps
  exact ⟨by simp [onTier, h1], by simp [onTier, h2]⟩

/-- Once there is a path, the tier route takes no more machine transitions
than the interpreted one. -/
theorem onTier_steps_le (c d : Nat) (k : α → Option β) (ps : List α)
    (h : ps ≠ []) : (onTier d k ps).1 ≤ (interpreted c k ps).1 := by
  rw [(onTier_steps d k ps).1, interpreted_steps]
  have : 1 ≤ ps.length := List.length_pos_iff.mpr h
  nlinarith

/-- With every path filtered out, the interpreted route takes `(c + 1) * P`
machine transitions for `P` paths, and the tier route one. -/
theorem interpreted_unbounded (c d : Nat) (ps : List α) :
    (interpreted c (fun _ => (none : Option β)) ps).1 = (c + 1) * ps.length ∧
    (onTier d (fun _ => (none : Option β)) ps).1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [interpreted_steps]; simp
  · rw [(onTier_steps d _ ps).1]; simp

end Mettapedia.Machines.QueryBodyOnTier
