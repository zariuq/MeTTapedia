import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# The evaluator of a transform-calculus run over a ground occurrence store

This is the first stage of the derivation of the abstract machine and the instruction set of the
transform calculus by the functional correspondence (Ager, Biernacki, Danvy and Midtgaard): a
direct-style evaluator, written as ordinary Lean functions. Later stages transform it into
continuation-passing style, defunctionalize its continuations, and read the abstract machine and
its instructions off the result.

## What it evaluates

Rules are the step theory's own rules at one frame (`RuleSyntax.Rule (OneFrame.Terms T)`): take
patterns, read patterns, tells, checks (equation guards, predicate queries, counts), collect
patterns and produced terms. The store is a list of occurrences, each an identity and a ground
value, with a supply of fresh identities. Term syntax enters only through a `Matcher`: extending
bindings by matching a pattern against a ground value, and instantiating a term under bindings.

* A rule is read as a list of goals solved from left to right (`goals`): its take premises, its
  read premises, then its determinate goals (tells, checks, collect patterns, produced terms).
* `solve` lists every match of a goal list in order: a premise chooses each occurrence of the
  store in turn; a determinate goal has at most one solution.
* `firings` lists every firing of a program: rules in order, each rule's matches in order.
* `publish` removes the taken occurrences, then adds the made values under fresh identities.
* `run` is one run under the scheduler that fires the first firing: it publishes the first firing
  and continues, until no firing remains (`quiescent`) or the allowance of firings is spent
  (`exhausted`). A store with no firing is quiescent at every allowance.

The step theory's admission is proved to be exactly what `firings` enumerates in
`Derivation.StepAdequacy`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe u v w

/-- **Matching against ground values.** `extend` matches a pattern against a ground value under the
bindings so far; `instantiate` reads a term under bindings as a ground value, when the bindings
determine it. -/
structure Matcher (T : Type u) (V : Type v) (B : Type w) where
  empty : B
  extend : B → T → V → Option B
  instantiate : B → T → Option V

/-- How a premise uses the occurrence it matches: a take consumes it, a read keeps it. -/
inductive Role where
  | take
  | read
  deriving DecidableEq, Repr

/-- The goals of a rule that do not choose an occurrence: they have at most one solution. -/
inductive Determinate (T : Type u) where
  | tell (left right : T)
  | check (guard : Check T)
  | collect (pattern : T)
  | produce (template : T)

/-- A goal of a rule: a premise, matched against an occurrence of the store, or a determinate
goal. -/
inductive Goal (T : Type u) where
  | premise (role : Role) (pattern : T)
  | determinate (goal : Determinate T)

/-- The step theory's rules at one frame. -/
abbrev Rule (T : Type u) := RuleSyntax.Rule (RuleSyntax.OneFrame.Terms T)

/-- **A rule as goals**: its take premises, its read premises, its tells, its checks, its collect
patterns and its produced terms, in this order. -/
def goals {T : Type u} (r : Rule T) : List (Goal T) :=
  r.body.take.map (Goal.premise .take) ++ r.body.read.map (Goal.premise .read) ++
    r.body.tell.map (fun e => Goal.determinate (.tell e.1 e.2)) ++
    r.body.checks.map (fun c => Goal.determinate (.check c)) ++
    r.collect.map (fun p => Goal.determinate (.collect p)) ++
    r.body.produce.map (fun t => Goal.determinate (.produce t))

/-- **The store**: occurrences in order, each an identity and a ground value, and the next fresh
identity. -/
structure Store (V : Type v) where
  occurrences : List (ℕ × V)
  fresh : ℕ
  deriving DecidableEq, Repr

namespace Store

variable {V : Type v}

/-- Remove the occurrence with an identity. -/
def remove (s : Store V) (o : ℕ) : Store V :=
  ⟨s.occurrences.filter (fun x => x.1 != o), s.fresh⟩

/-- Add an occurrence of a value under the next fresh identity. -/
def add (s : Store V) (value : V) : Store V :=
  ⟨s.occurrences ++ [(s.fresh, value)], s.fresh + 1⟩

/-- Remove occurrences, one after another. -/
def takeAll : Store V → List ℕ → Store V
  | s, [] => s
  | s, o :: os => takeAll (s.remove o) os

/-- Add values, one after another. -/
def makeAll : Store V → List V → Store V
  | s, [] => s
  | s, w :: ws => makeAll (s.add w) ws

/-- The identities of the occurrences carrying a value, in order. -/
def carrying [DecidableEq V] (s : Store V) (value : V) : List ℕ :=
  (s.occurrences.filter (fun x => decide (x.2 = value))).map Prod.fst

/-- Identities are distinct and below the fresh identity. -/
def WellFormed (s : Store V) : Prop :=
  (s.occurrences.map Prod.fst).Nodup ∧ ∀ x ∈ s.occurrences, x.1 < s.fresh

/-- The identities present. -/
def ids (s : Store V) : List ℕ := s.occurrences.map Prod.fst

end Store

/-- **A match so far**: bindings, the occurrences taken and read in pattern order, the sets seen by
the collect patterns, and the made values. -/
structure Match (V : Type v) (B : Type w) where
  bindings : B
  taken : List ℕ
  read : List ℕ
  seen : List (Finset ℕ)
  made : List V

namespace Match

variable {T : Type u} {V : Type v} {B : Type w}

/-- The empty match of a rule. -/
def start (M : Matcher T V B) : Match V B := ⟨M.empty, [], [], [], []⟩

/-- Record the occurrence a premise matched, with the extended bindings. -/
def select (m : Match V B) : Role → ℕ → B → Match V B
  | .take, o, θ => {m with bindings := θ, taken := m.taken ++ [o]}
  | .read, o, θ => {m with bindings := θ, read := m.read ++ [o]}

end Match

/-- Which occurrences a premise may use: a take neither a taken nor a read occurrence, a read any
occurrence not taken. Reads may share an occurrence; consumption may not. -/
def Role.allows {V : Type v} {B : Type w} : Role → Match V B → ℕ → Bool
  | .take, m, o => !(m.taken.contains o) && !(m.read.contains o)
  | .read, m, o => !(m.taken.contains o)

section Goals

variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] (M : Matcher T V B)

/-- **A premise at one occurrence**: the occurrence is allowed and the pattern matches its value. -/
def attempt (role : Role) (pattern : T) (m : Match V B) (x : ℕ × V) : Option (Match V B) :=
  if role.allows m x.1 then (M.extend m.bindings pattern x.2).map (m.select role x.1) else none

/-- Both sides instantiate to one value. -/
def agree (θ : B) (left right : T) : Bool :=
  match M.instantiate θ left, M.instantiate θ right with
  | some a, some b => decide (a = b)
  | _, _ => false

/-- **A check under bindings at a store**: an equation guard, a predicate query over the values of
the store, or a count of the occurrences carrying a value. -/
def passes (s : Store V) (θ : B) : Check T → Bool
  | .equal left right => agree M θ left right
  | .predicate .any pattern =>
      match M.instantiate θ pattern with
      | some w => s.occurrences.any (fun x => decide (x.2 = w))
      | none => false
  | .predicate .none pattern =>
      match M.instantiate θ pattern with
      | some w => !(s.occurrences.any (fun x => decide (x.2 = w)))
      | none => false
  | .count pattern number =>
      match M.instantiate θ pattern with
      | some w => decide (s.occurrences.countP (fun x => decide (x.2 = w)) = number)
      | none => false

/-- **A determinate goal**: a tell is solved when its sides agree, a check when it passes; a collect
pattern records the occurrences carrying its value; a produced term records its value. -/
def Determinate.apply (s : Store V) : Determinate T → Match V B → Option (Match V B)
  | .tell left right, m => if agree M m.bindings left right then some m else none
  | .check c, m => if passes M s m.bindings c then some m else none
  | .collect pattern, m =>
      (M.instantiate m.bindings pattern).map fun w => {m with seen := m.seen ++ [(s.carrying w).toFinset]}
  | .produce template, m =>
      (M.instantiate m.bindings template).map fun w => {m with made := m.made ++ [w]}

/-- **Every match of a goal list**, in order: a premise tries the occurrences of the store in
order, a determinate goal has at most one solution. -/
def solve (s : Store V) : List (Goal T) → Match V B → List (Match V B)
  | [], m => [m]
  | .premise role pattern :: gs, m =>
      s.occurrences.flatMap fun x =>
        match attempt M role pattern m x with
        | some m' => solve s gs m'
        | none => []
  | .determinate d :: gs, m =>
      match d.apply M s m with
      | some m' => solve s gs m'
      | none => []

/-- **Every firing of a program at a store**: rules in order, each with its matches in order. -/
def firings (P : List (Rule T)) (s : Store V) : List (Rule T × Match V B) :=
  P.flatMap fun r => (solve M s (goals r) (Match.start M)).map fun m => (r, m)

end Goals

/-- **Publication**: remove the taken occurrences, then add the made values under fresh
identities. -/
def publish {V : Type v} {B : Type w} (s : Store V) (m : Match V B) : Store V :=
  (s.takeAll m.taken).makeAll m.made

/-- How a run ends: no firing remains, or a firing remains when the allowance is spent. -/
inductive Outcome (V : Type v) where
  | quiescent (s : Store V)
  | exhausted (s : Store V)
  deriving DecidableEq, Repr

section Run

variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] (M : Matcher T V B)
  (P : List (Rule T))

/-- The stores one firing reaches, in the order of `firings`. -/
def successors (s : Store V) : List (Store V) :=
  (firings M P s).map fun f => publish s f.2

/-- **A run under the scheduler that fires the first firing**, with an allowance of firings. -/
def run : ℕ → Store V → Outcome V
  | 0, s =>
      match firings M P s with
      | [] => .quiescent s
      | _ :: _ => .exhausted s
  | a + 1, s =>
      match firings M P s with
      | [] => .quiescent s
      | f :: _ => run a (publish s f.2)

theorem run_quiescent (a : ℕ) (s : Store V) (none : firings M P s = []) :
    run M P a s = .quiescent s := by
  cases a <;> simp [run, none]

theorem run_succ_fire (a : ℕ) (s : Store V) (f : Rule T × Match V B)
    (rest : List (Rule T × Match V B)) (first : firings M P s = f :: rest) :
    run M P (a + 1) s = run M P a (publish s f.2) := by
  simp [run, first]

theorem run_zero_fire (s : Store V) (f : Rule T × Match V B)
    (rest : List (Rule T × Match V B)) (first : firings M P s = f :: rest) :
    run M P 0 s = .exhausted s := by
  simp [run, first]

end Run

/-! ## Closed forms of publication -/

namespace Store

variable {V : Type v}

theorem takeAll_occurrences (s : Store V) (os : List ℕ) :
    (s.takeAll os).occurrences = s.occurrences.filter (fun x => !(os.contains x.1)) ∧
      (s.takeAll os).fresh = s.fresh := by
  induction os generalizing s with
  | nil => simp [takeAll]
  | cons o os ih =>
      obtain ⟨occurrences, fresh⟩ := ih (s.remove o)
      refine ⟨?_, fresh⟩
      rw [takeAll, occurrences]
      simp only [remove, List.filter_filter]
      congr 1
      funext x
      simp only [List.contains_cons, Bool.not_or, bne]
      exact Bool.and_comm _ _

theorem makeAll_occurrences (s : Store V) (ws : List V) :
    (s.makeAll ws).occurrences =
        s.occurrences ++ ws.zipIdx.map (fun x => (s.fresh + x.2, x.1)) ∧
      (s.makeAll ws).fresh = s.fresh + ws.length := by
  induction ws generalizing s with
  | nil => simp [makeAll]
  | cons w ws ih =>
      obtain ⟨occurrences, fresh⟩ := ih (s.add w)
      refine ⟨?_, ?_⟩
      · rw [makeAll, occurrences]
        simp only [add, List.append_assoc, List.zipIdx_cons, List.map_cons, Nat.add_zero,
          List.singleton_append]
        congr 2
        rw [List.zipIdx_succ, List.map_map]
        apply List.map_congr_left
        intro x _
        simp only [Function.comp_apply, Prod.mk.injEq, and_true]
        omega
      · rw [makeAll, fresh]
        simp only [add, List.length_cons]
        omega

end Store

theorem publish_occurrences {V : Type v} {B : Type w} (s : Store V) (m : Match V B) :
    (publish s m).occurrences =
        s.occurrences.filter (fun x => !(m.taken.contains x.1)) ++
          m.made.zipIdx.map (fun x => (s.fresh + x.2, x.1)) ∧
      (publish s m).fresh = s.fresh + m.made.length := by
  obtain ⟨taken, takenFresh⟩ := Store.takeAll_occurrences s m.taken
  obtain ⟨made, madeFresh⟩ := Store.makeAll_occurrences (s.takeAll m.taken) m.made
  refine ⟨?_, ?_⟩
  · rw [publish, made, taken, takenFresh]
  · rw [publish, madeFresh, takenFresh]

end Mettapedia.Machines.TIsa.Derivation
