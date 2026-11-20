import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# A core with explicit quotation, running, return and binding

One core calculus into which every evaluation mode below is elaborated. Its data are the tree's
MeTTa atoms (`OSLFCore.Atom`); a template is an atom whose variables the environment instantiates.

* `ret t` returns the instance of the template `t` as a value: this is quotation, the text comes
  back as written with its variables filled in.
* `bind c x k` runs `c` and runs `k` once per answer with `x` bound to it (call-by-push-value's
  `to`).
* `run t` runs the instance of `t` as code. What "as code" means is the program's `code` map, which
  an elaboration supplies: the surface's own reading of a text at a computation position.
* `call f args` enters the definition of `f` with data arguments. The definition matches its
  clauses one way, checks its declared argument and result kinds, and records `f` on the trace of
  every answer (so a run's cost in calls of `f` can be read off).
* `plus a b` is the grounded `+` on two data; on non-numbers it returns the unreduced call.

The evaluator `exec` takes fuel; running out is `none`, its own outcome, never an empty answer.
Every alternative keeps its own trace; answers are listed in program order (a bag read as a list).
A refused check is an explicit answer (`Out.refused`), so a later observation decides whether it
prints as an error or as no answer.

Nothing here knows about declared types `Atom`, `Proc` or `%Undefined%`: an elaboration decides
where `run` and `ret` go.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

namespace Core

/-- The data bound to each variable, newest first. -/
abbrev Env := List (String × Atom)

/-- Instantiate a template: each variable bound in the environment is replaced by its datum; an
unbound variable stays as written. -/
def inst (ρ : Env) : Atom → Atom
  | .var x => (ρ.lookup x).getD (.var x)
  | .expression items => .expression (instList ρ items)
  | a => a
where
  /-- Instantiate each item of a list. -/
  instList (ρ : Env) : List Atom → List Atom
    | [] => []
    | a :: as => inst ρ a :: instList ρ as

/-- A check that a declared value type makes on a datum. -/
inductive Kind where
  | number
  | bool
  deriving DecidableEq, Repr

/-- Whether a datum passes a check. -/
def Kind.accepts : Kind → Atom → Bool
  | .number, .grounded (.int _) => true
  | .bool, .symbol name => name == "True" || name == "False"
  | _, _ => false

/-- The type a check names, for printing a refusal. -/
def Kind.name : Kind → Atom
  | .number => .symbol "Number"
  | .bool => .symbol "Bool"

/-- One outcome of a branch: a value, or a datum that a declared check refused. -/
inductive Out where
  | val (datum : Atom)
  | refused (datum : Atom) (kind : Kind)
  deriving DecidableEq, Repr

/-- An answer: its outcome and the heads entered on its branch, in order. -/
abbrev Ans := Out × List String

/-- Computations. -/
inductive Comp where
  /-- Return the instance of a template (quotation). -/
  | ret (template : Atom)
  /-- Run the first computation and the rest once per answer, binding the answer. -/
  | bind (first : Comp) (name : String) (rest : Comp)
  /-- Run the instance of a template as code. -/
  | run (template : Atom)
  /-- Enter a definition with the instances of the argument templates. -/
  | call (head : String) (args : List Atom)
  /-- The grounded `+`. -/
  | plus (left right : Atom)
  deriving DecidableEq, Repr

/-- A definition: its head and arity, the kind checks on its arguments and on its results, and its
clauses (argument patterns and a body over the patterns' variables). -/
structure Def where
  head : String
  arity : Nat
  argChecks : List (Option Kind)
  resultCheck : Option Kind
  clauses : List (List Atom × Comp)

/-- A program: definitions, and the reading of a datum as code that `run` uses. -/
structure Prog where
  defs : List Def
  code : Atom → Comp

/-- The first definition with this head and arity. -/
def Prog.find (P : Prog) (head : String) (arity : Nat) : Option Def :=
  P.defs.find? fun d => d.head == head && d.arity == arity

/-- One-way matching of a pattern against a datum, extending the bindings; a variable already bound
must meet an equal datum. -/
def matchAtom : Atom → Atom → Env → Option Env
  | .var x, d, ρ =>
      match ρ.lookup x with
      | some e => if e = d then some ρ else none
      | none => some ((x, d) :: ρ)
  | .expression ps, .expression ds, ρ => matchList ps ds ρ
  | p, d, ρ => if p = d then some ρ else none
where
  /-- Match patterns against data, item by item. -/
  matchList : List Atom → List Atom → Env → Option Env
    | [], [], ρ => some ρ
    | p :: ps, d :: ds, ρ =>
        match matchAtom p d ρ with
        | some ρ' => matchList ps ds ρ'
        | none => none
    | _, _, _ => none

/-- The grounded `+`: the sum of two integers, otherwise the unreduced call. -/
def plusData : Atom → Atom → Atom
  | .grounded (.int a), .grounded (.int b) => .grounded (.int (a + b))
  | a, b => .expression [.symbol "+", a, b]

/-- The first argument that its declared check refuses. -/
def firstRefusal : List (Option Kind) → List Atom → Option (Atom × Kind)
  | some k :: ks, a :: as => if k.accepts a then firstRefusal ks as else some (a, k)
  | none :: ks, _ :: as => firstRefusal ks as
  | _, _ => none

/-- Apply a declared result check to an outcome. -/
def checkResult : Option Kind → Out → Out
  | some k, .val d => if k.accepts d then .val d else .refused d k
  | _, o => o

/-- Continue every value answer with `k`, prefixing its trace; a refusal stays an answer and is not
continued. -/
def continueEach (k : Atom → Option (List Ans)) : List Ans → Option (List Ans)
  | [] => some []
  | (.val v, trace) :: rest =>
      match k v, continueEach k rest with
      | some here, some later => some (here.map (fun a => (a.1, trace ++ a.2)) ++ later)
      | _, _ => none
  | (.refused d kind, trace) :: rest =>
      (continueEach k rest).map ((.refused d kind, trace) :: ·)

/-- Run every clause whose patterns match, in program order. -/
def runClauses (ev : Env → Comp → Option (List Ans)) (args : List Atom) :
    List (List Atom × Comp) → Option (List Ans)
  | [] => some []
  | (pats, body) :: rest =>
      match matchAtom.matchList pats args [], runClauses ev args rest with
      | some ρ, some later => (ev ρ body).map (· ++ later)
      | none, some later => some later
      | _, none => none

/-- Whether some clause matches the arguments. -/
def anyClauseMatches (args : List Atom) (clauses : List (List Atom × Comp)) : Bool :=
  clauses.any fun c => (matchAtom.matchList c.1 args []).isSome

/-- What the evaluator is asked to do: run a computation in an environment, or enter a head. -/
inductive Goal where
  | comp (env : Env) (c : Comp)
  | enter (head : String) (args : List Atom)

/-- The evaluator. A call of a head without a definition, or whose clauses all fail to match,
returns the call itself (Hyperon Experimental's convention); fuel that runs out is `none`. -/
def exec (P : Prog) : Nat → Goal → Option (List Ans)
  | 0, _ => none
  | _ + 1, .comp ρ (.ret t) => some [(.val (inst ρ t), [])]
  | n + 1, .comp ρ (.bind c x k) =>
      match exec P n (.comp ρ c) with
      | none => none
      | some first => continueEach (fun v => exec P n (.comp ((x, v) :: ρ) k)) first
  | n + 1, .comp ρ (.run t) => exec P n (.comp [] (P.code (inst ρ t)))
  | n + 1, .comp ρ (.call f args) => exec P n (.enter f (args.map (inst ρ)))
  | _ + 1, .comp ρ (.plus a b) => some [(.val (plusData (inst ρ a) (inst ρ b)), [])]
  | n + 1, .enter f args =>
      match P.find f args.length with
      | none => some [(.val (.expression (.symbol f :: args)), [])]
      | some d =>
          match firstRefusal d.argChecks args with
          | some (a, k) => some [(.refused a k, [f])]
          | none =>
              if anyClauseMatches args d.clauses then
                (runClauses (fun ρ c => exec P n (.comp ρ c)) args d.clauses).map
                  (List.map fun a => (checkResult d.resultCheck a.1, f :: a.2))
              else some [(.val (.expression (.symbol f :: args)), [f])]

/-- What a run prints: each value, and each refusal either as an error atom or not at all. -/
def observe (reportsRefusal : Bool) : List Ans → List Atom
  | [] => []
  | (.val d, _) :: rest => d :: observe reportsRefusal rest
  | (.refused d k, _) :: rest =>
      if reportsRefusal then
        .expression [.symbol "Error", d, .expression [.symbol "BadType", k.name]] ::
          observe reportsRefusal rest
      else observe reportsRefusal rest

/-- Whether an outcome is a value. -/
def Out.isVal : Out → Bool
  | .val _ => true
  | .refused _ _ => false

/-- No answer is a refusal (no check refused anything on any branch). -/
def allVal (L : List Ans) : Bool := L.all fun a => a.1.isVal

/-! ## Basic laws of the core -/

theorem exec_ret (P : Prog) (n : Nat) (ρ : Env) (t : Atom) :
    exec P (n + 1) (.comp ρ (.ret t)) = some [(.val (inst ρ t), [])] := rfl

theorem exec_bind (P : Prog) (n : Nat) (ρ : Env) (c k : Comp) (x : String) :
    exec P (n + 1) (.comp ρ (.bind c x k)) =
      (exec P n (.comp ρ c)).bind
        (continueEach fun v => exec P n (.comp ((x, v) :: ρ) k)) := by
  simp only [exec]
  cases exec P n (.comp ρ c) <;> rfl

theorem exec_run (P : Prog) (n : Nat) (ρ : Env) (t : Atom) :
    exec P (n + 1) (.comp ρ (.run t)) = exec P n (.comp [] (P.code (inst ρ t))) := rfl

theorem exec_call (P : Prog) (n : Nat) (ρ : Env) (f : String) (args : List Atom) :
    exec P (n + 1) (.comp ρ (.call f args)) = exec P n (.enter f (args.map (inst ρ))) := rfl

theorem inst_var_head (ρ : Env) (x : String) (v : Atom) :
    inst ((x, v) :: ρ) (.var x) = v := by
  simp [inst, List.lookup]

/-- Continuing every value with its own return is the identity. -/
theorem continueEach_return (L : List Ans) :
    continueEach (fun v => some [(.val v, [])]) L = some L := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨o, trace⟩ := a
      cases o with
      | val v => simp [continueEach, ih]
      | refused d k => simp [continueEach, ih]

/-- **The right unit law of the core** (`bind c x (ret x)` is `c`), with the step that `bind`
takes. -/
theorem exec_bind_ret (P : Prog) (n : Nat) (ρ : Env) (c : Comp) (x : String) :
    exec P (n + 2) (.comp ρ (.bind c x (.ret (.var x)))) = exec P (n + 1) (.comp ρ c) := by
  rw [exec_bind]
  have hk : (fun v => exec P (n + 1) (.comp ((x, v) :: ρ) (.ret (.var x)))) =
      fun v => some [(.val v, [])] := by
    funext v
    rw [exec_ret, inst_var_head]
  rw [hk]
  cases exec P (n + 1) (.comp ρ c) with
  | none => rfl
  | some L => exact continueEach_return L

/-- Continuing every value with a fixed one-answer continuation appends that answer's trace. -/
theorem continueEach_single (L : List Ans) (f : String) :
    continueEach (fun v => some [(.val v, [f])]) L =
      some (L.map fun a => match a with
        | (.val v, trace) => (.val v, trace ++ [f])
        | (.refused d k, trace) => (.refused d k, trace)) := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨o, trace⟩ := a
      cases o with
      | val v => simp [continueEach, ih]
      | refused d k => simp [continueEach, ih]

/-- Observation forgets traces. -/
theorem observe_appendTrace (b : Bool) (L : List Ans) (f : String) :
    observe b (L.map fun a => match a with
        | (.val v, trace) => (.val v, trace ++ [f])
        | (.refused d k, trace) => (.refused d k, trace)) = observe b L := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨o, trace⟩ := a
      cases o with
      | val v => simp [observe, ih]
      | refused d k =>
          cases b <;> simp [observe, ih]

end Core

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
