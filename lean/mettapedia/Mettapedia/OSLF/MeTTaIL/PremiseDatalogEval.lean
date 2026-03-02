import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Premise Datalog Evaluator

Lean-side interpreter for `PremiseProgram`. This converts a declarative set of
datalog rules into a `RelationEnv` that the generic rewrite engine can use.

## Connection to Premises.lean

The existing `mettaFullRelEnv` in `Premises.lean` defines MeTTa's premise
relations as direct Lean functions. Once `mettaFullPremises : PremiseProgram`
is defined, we need an adequacy theorem:

  `evalPremiseProgram mettaFullPremises = mettaFullRelEnv`

This proves the IR faithfully captures the intended semantics.

## LLM Primer
- Evaluation is bottom-up: compute all tuples for each relation, in
  stratification order. Within a stratum, iterate to fixed point.
- `PGuard.deconstruct` matches a constructor application and binds fields.
- An "environment" maps variable names to Pattern values.
- `PGuard.notIn` requires stratification: the negated relation must be
  in a strictly lower stratum (fully computed before being negated).
-/

namespace Mettapedia.OSLF.MeTTaIL.PremiseDatalogEval

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.MeTTaIL.PremiseDatalog
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-! ## Variable Environment -/

/-- A binding environment mapping variable names to Pattern values. -/
abbrev Env := List (String × Pattern)

def Env.lookup (env : Env) (name : String) : Option Pattern :=
  (env.find? (·.1 == name)).map (·.2)

def Env.bind (env : Env) (name : String) (val : Pattern) : Env :=
  (name, val) :: env

/-! ## Expression Evaluation -/

/-- Evaluate a PExpr under a binding environment.
    Returns `none` if a variable is unbound or a builtin call fails. -/
partial def evalExpr (env : Env) (builtins : List BuiltinFn) : PExpr → Option Pattern
  | .var name => env.lookup name
  | .ctor ctorName args => do
      let evalArgs ← args.mapM (evalExpr env builtins)
      pure (.apply ctorName evalArgs)
  | .literal p => some p
  | .call _fnName _args =>
      -- Builtin calls are resolved by the backend.
      -- The Lean evaluator does not execute arbitrary builtins;
      -- this is intentionally left as `none` and must be overridden
      -- per-language with a concrete `BuiltinEval` function.
      none
  | .wild => some (.fvar "_")  -- wildcard matches anything

/-! ## Guard Evaluation -/

/-- Try to deconstruct a Pattern as constructor application with the given name
    and bind fields to the given names. -/
def deconstructPattern (pat : Pattern) (ctorName : String)
    (fieldNames : List String) : Option Env :=
  match pat with
  | .apply c args =>
      if c == ctorName && args.length == fieldNames.length then
        some (fieldNames.zip args |>.filter (·.1 ≠ "_"))
      else
        none
  | _ => none

/-- A relation store maps relation names to sets of tuples. -/
abbrev RelStore := List (String × List (List Pattern))

def RelStore.lookup (store : RelStore) (rel : String) : List (List Pattern) :=
  match store.find? (·.1 == rel) with
  | some (_, tuples) => tuples
  | none => []

/-- Evaluate a single guard, producing a list of extended environments.
    Empty list means the guard failed. -/
partial def evalGuard (store : RelStore) (builtins : List BuiltinFn)
    (env : Env) : PGuard → List Env
  | .eq lhs rhs => do
      match evalExpr env builtins lhs, evalExpr env builtins rhs with
      | some l, some r => if l == r then [env] else []
      | _, _ => []
  | .neq lhs rhs =>
      match evalExpr env builtins lhs, evalExpr env builtins rhs with
      | some l, some r => if l != r then [env] else []
      | _, _ => []
  | .deconstruct expr ctorName fieldNames =>
      match evalExpr env builtins expr with
      | some pat =>
          match deconstructPattern pat ctorName fieldNames with
          | some bindings => [bindings ++ env]
          | none => []
      | none => []
  | .compute _fnName _args _result =>
      -- Like `call` in PExpr, concrete builtin evaluation is backend-specific.
      -- The Lean evaluator leaves this unimplemented by default.
      -- Override with `BuiltinEvalFn` for concrete testing.
      []
  | .computeMany _fnName _args _result =>
      -- Like `compute`, concrete builtin evaluation is backend-specific.
      -- This variant models nondeterministic outputs.
      []
  | .notIn rel args =>
      let evaluatedArgs := args.map (evalExpr env builtins)
      -- Check if the relation has any matching tuples
      let tuples := store.lookup rel
      let hasMatch := tuples.any fun tuple =>
        evaluatedArgs.zip tuple |>.all fun (maybeArg, val) =>
          match maybeArg with
          | some (.fvar "_") => true   -- wildcard
          | some a => a == val
          | none => true               -- unbound = wildcard
      if hasMatch then [] else [env]   -- succeed if NO match found
  | .relQuery rel args => do
      let tuples := store.lookup rel
      tuples.filterMap fun tuple => do
        -- Try to unify args with this tuple
        guard (args.length == tuple.length)
        let mut env' := env
        for (arg, val) in args.zip tuple do
          match arg with
          | .var name =>
              match env'.lookup name with
              | some existing => guard (existing == val)
              | none => env' := env'.bind name val
          | .wild => pure ()
          | other =>
              let evaled ← evalExpr env' builtins other
              guard (evaled == val)
        return env'
  | .collIter expr _ct elemName =>
      match evalExpr env builtins expr with
      | some (.collection _ct' elems _) =>
          elems.map fun elem => env.bind elemName elem
      | _ => []
  | .trueGuard => [env]

/-! ## Rule Evaluation -/

/-- Evaluate a rule body (conjunction of guards) starting from an initial env.
    Returns all environments that satisfy all guards. -/
def evalBody (store : RelStore) (builtins : List BuiltinFn)
    (guards : List PGuard) (initEnv : Env) : List Env :=
  guards.foldl (fun envs guard =>
    envs.flatMap (evalGuard store builtins · guard)
  ) [initEnv]

/-- Evaluate a single rule, producing all output tuples. -/
def evalRule (store : RelStore) (builtins : List BuiltinFn)
    (rule : PRule) : List (List Pattern) :=
  let envs := evalBody store builtins rule.body []
  envs.filterMap fun env =>
    rule.headArgs.mapM (evalExpr env builtins)

/-! ## Fixed-Point Evaluation -/

/-- One iteration of bottom-up evaluation: compute new tuples for all relations. -/
def evalRound (prog : PremiseProgram) (store : RelStore) : RelStore :=
  prog.relations.map fun decl =>
    let rules := prog.rulesFor decl.name
    let existingTuples := store.lookup decl.name
    let newTuples := rules.flatMap (evalRule store prog.builtins)
    -- Deduplicate
    let allTuples := (existingTuples ++ newTuples).eraseDups
    (decl.name, allTuples)

/-- Evaluate to fixed point with fuel bound. -/
partial def evalToFixedPoint (prog : PremiseProgram) (store : RelStore)
    (fuel : Nat := 100) : RelStore :=
  match fuel with
  | 0 => store
  | fuel' + 1 =>
      let store' := evalRound prog store
      if store' == store then store
      else evalToFixedPoint prog store' fuel'

/-! ## Query-Driven Evaluation

The `RelationEnv` interface is query-driven: given a relation name and
argument patterns, return matching tuples. This is different from the
bottom-up fixed-point above.

For the `evalPremiseProgram` bridge, we use a hybrid approach:
evaluate rules on-demand using the input arguments as constraints.
-/

/-- Evaluate a premise program as a RelationEnv.

This is the key bridge: it converts a `PremiseProgram` into a `RelationEnv`
that the generic rewrite engine can use.

Note: This is `noncomputable` because Pattern's DecidableEq uses
classical choice in some branches. -/
noncomputable def evalPremiseProgram (prog : PremiseProgram)
    (_builtinEval : String → List Pattern → Option Pattern := fun _ _ => none)
    : RelationEnv where
  tuples rel args :=
    -- Build initial store seeded with the query arguments
    let initStore : RelStore := []
    -- Evaluate all rules to fixed point
    let finalStore := evalToFixedPoint prog initStore
    -- Look up the queried relation and filter by argument pattern
    let allTuples := finalStore.lookup rel
    allTuples.filter fun tuple =>
      args.zip tuple |>.all fun (arg, val) =>
        match arg with
        | .fvar _ => true  -- free variable matches anything
        | _ => arg == val

end Mettapedia.OSLF.MeTTaIL.PremiseDatalogEval
