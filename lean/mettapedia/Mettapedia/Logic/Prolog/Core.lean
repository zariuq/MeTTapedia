import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Prolog Goal Language

This module defines the **Prolog goal language** used by PeTTa's `translate_expr`
compiler, along with evaluation environments (`PEnv`).

Prolog (for our purposes) = LP (pure Horn clauses, already in `Logic.LP`) PLUS
the following **built-in goal constructors**:

| Constructor | Prolog | Semantics |
|-------------|--------|-----------|
| `succeed`   | `true` | always succeeds |
| `fail`      | `fail` | always fails |
| `cut`       | `!`    | pruning (first alternative only) |
| `conj`      | `G1, G2` | sequence |
| `disj`      | `G1 ; G2` | nondeterministic choice |
| `ite`       | `C -> T ; E` | if-then-else |
| `once`      | `once(G)` | at most one answer |
| `neg`       | `\+ G` | negation-as-failure |
| `isVar`     | `var(P)` | succeeds iff `P` is an unbound variable |
| `unify`     | `P = Q` | pattern unification |
| `notUnify`  | `P \= Q` | unification failure |
| `findall`   | `findall(V, G, Vs)` | all-answers collection |
| `spaceMatch`| `match(&self, P, Body)` | space lookup |
| `reduceCall`| `reduce([F|Args], Out)` | MeTTa evaluator |

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed. (1987)
- Sterling & Shapiro, *The Art of Prolog*, 2nd ed. (1994)
- PeTTa `translator.pl`: the `translate_expr/3` predicate
-/

namespace Mettapedia.Logic.Prolog

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Prolog Environments -/

/-- A Prolog evaluation environment: maps (Prolog) variable names to Pattern values.

    Prolog variables in the generated goals of `translate_expr` correspond to
    intermediate values bound during evaluation.  We represent them as a
    `List (String × Pattern)` association list; later bindings shadow earlier ones. -/
abbrev PEnv := List (String × Pattern)

namespace PEnv

/-- Look up a variable in the environment (first match wins). -/
def lookup (env : PEnv) (v : String) : Option Pattern :=
  (env.find? (fun ⟨k, _⟩ => k == v)).map Prod.snd

/-- Extend the environment by binding `v ↦ p` (shadows any prior binding of `v`). -/
def insert (env : PEnv) (v : String) (p : Pattern) : PEnv :=
  (v, p) :: env

/-- The empty environment. -/
def empty : PEnv := []

end PEnv

/-! ## Encoding Lists of Patterns as Patterns -/

/-- Encode a `List Pattern` as a Pattern using `cons`/`nil` constructors.

    Used by `findall` to return the collected answer list as a single Pattern value.
    Matches Prolog's standard list encoding: `[H|T]` = `cons(H, T)`, `[]` = `nil`. -/
def Pattern.mkList : List Pattern → Pattern
  | []      => .apply "[]" []
  | (x :: xs) => .apply "[|]" [x, Pattern.mkList xs]

@[simp]
theorem Pattern.mkList_nil : Pattern.mkList [] = .apply "[]" [] := rfl

@[simp]
theorem Pattern.mkList_cons (x : Pattern) (xs : List Pattern) :
    Pattern.mkList (x :: xs) = .apply "[|]" [x, Pattern.mkList xs] := rfl

/-! ## Prolog Goal Language -/

/-- A Prolog goal parameterized by its **reduce oracle** type `ρ`.

    The oracle type `ρ` is abstract here; it is instantiated to `PeTTaSpace`
    in `Eval.lean` when we wire `reduceCall` to `PeTTaEval`.

    All constructors correspond to Prolog built-ins used by `translate_expr`. -/
inductive PrologGoal where
  /-- `true` — always succeeds once, unchanged environment. -/
  | succeed : PrologGoal

  /-- `fail` — always fails, no answers. -/
  | fail : PrologGoal

  /-- `!` (cut) — succeeds once and prunes remaining alternatives in the
      enclosing disjunction or clause choice point.

      **Implementation note**: cut's effect is scoped to the nearest enclosing
      disjunction (`disj`) or clause-selection context.  Semantics follow the
      standard Prolog cut barrier: cut propagates through `conj` but is caught
      by `disj` and `findall`. -/
  | cut : PrologGoal

  /-- `G1, G2` — conjunction: run `G1`, then `G2` for each answer from `G1`. -/
  | conj : PrologGoal → PrologGoal → PrologGoal

  /-- `G1 ; G2` — disjunction: nondeterministic choice between `G1` and `G2`.
      Also serves as the catch point for `cut` propagating up from `G1`. -/
  | disj : PrologGoal → PrologGoal → PrologGoal

  /-- `(Cond -> Then ; Else)` — if-then-else.
      If `Cond` has at least one answer, use the first (committing) and run `Then`;
      otherwise run `Else`. -/
  | ite : PrologGoal → PrologGoal → PrologGoal → PrologGoal

  /-- `once(G)` — take at most one answer from `G` (without cut side-effects). -/
  | once : PrologGoal → PrologGoal

  /-- `\+ G` — negation-as-failure: succeeds iff `G` has no answers. -/
  | neg : PrologGoal → PrologGoal

  /-- `var(P)` — succeeds iff `P` is an unbound variable under current environment. -/
  | isVar : Pattern → PrologGoal

  /-- `P = Q` — unify two patterns. Succeeds (extending the environment) iff
      `P` and `Q` can be unified via `matchPattern`. -/
  | unify : Pattern → Pattern → PrologGoal

  /-- `P \= Q` — fails iff `P` and `Q` can be unified; succeeds otherwise. -/
  | notUnify : Pattern → Pattern → PrologGoal

  /-- `findall(Var, Goal, _)` — all-solutions collection.
      Runs `Goal` to get all answer environments, extracts the value of `Var`
      from each, assembles a Pattern list, and returns it as a singleton answer
      with `Var` bound to that list.

      This formalizes `findall/3` for `collapse` and `foldall` in `translate_expr`. -/
  | findall : String → PrologGoal → PrologGoal

  /-- `match(&self, Pat, Tmpl)` — match `Pat` against the `&self` space,
      instantiate `Tmpl` with each binding set, return instantiated results.

      Unlike Prolog's general goal-running, this returns the instantiated
      template patterns directly (matching MeTTa's `(match &self pat tmpl)`
      semantics where the template is instantiated, not further evaluated).

      Formalizes the `match/3` built-in in translate_expr. -/
  | spaceMatch : Pattern → Pattern → PrologGoal

  /-- `reduce([F | Args], Out)` — invoke the MeTTa evaluator on `[F | Args]`
      and bind the result to `Out`.

      This is the **oracle call** that re-enters MeTTa evaluation; it makes
      `PrologEval` and `PeTTaEval` mutually recursive. -/
  | reduceCall : List Pattern → PrologGoal

deriving Repr

/-! ## Derived Constructors -/

/-- Build a left-associative conjunction chain from a list of goals.
    `conjList []` = `succeed`, `conjList [G]` = `G`, etc. -/
def conjList : List PrologGoal → PrologGoal
  | []      => .succeed
  | [g]     => g
  | (g :: gs) => .conj g (conjList gs)

/-- Build a left-associative disjunction chain from a list of goals.
    `disjList []` = `fail`, `disjList [G]` = `G`, etc. -/
def disjList : List PrologGoal → PrologGoal
  | []      => .fail
  | [g]     => g
  | (g :: gs) => .disj g (disjList gs)

@[simp]
theorem conjList_nil : conjList [] = .succeed := rfl

@[simp]
theorem conjList_singleton (g : PrologGoal) : conjList [g] = g := rfl

@[simp]
theorem disjList_nil : disjList [] = .fail := rfl

@[simp]
theorem disjList_singleton (g : PrologGoal) : disjList [g] = g := rfl

/-! ## Size / Well-Founded Recursion -/

/-- Syntactic size of a Prolog goal (for well-founded recursion). -/
def PrologGoal.size : PrologGoal → ℕ
  | .succeed       => 1
  | .fail          => 1
  | .cut           => 1
  | .conj g1 g2    => 1 + g1.size + g2.size
  | .disj g1 g2    => 1 + g1.size + g2.size
  | .ite c t e     => 1 + c.size + t.size + e.size
  | .once g        => 1 + g.size
  | .neg g         => 1 + g.size
  | .isVar _       => 1
  | .unify _ _     => 1
  | .notUnify _ _  => 1
  | .findall _ g   => 1 + g.size
  | .spaceMatch _ _ => 1
  | .reduceCall _  => 1

theorem PrologGoal.size_pos (g : PrologGoal) : 0 < g.size := by
  cases g <;> simp [PrologGoal.size]

theorem PrologGoal.conj_size_lt_left (g1 g2 : PrologGoal) :
    g1.size < (PrologGoal.conj g1 g2).size := by
  simp only [PrologGoal.size]; omega

theorem PrologGoal.conj_size_lt_right (g1 g2 : PrologGoal) :
    g2.size < (PrologGoal.conj g1 g2).size := by
  simp only [PrologGoal.size]; omega

end Mettapedia.Logic.Prolog
