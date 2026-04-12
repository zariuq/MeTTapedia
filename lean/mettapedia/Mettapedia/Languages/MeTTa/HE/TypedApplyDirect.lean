-- LLM primer: This formalizes interpret_function_args (eval.c:8440-8529).
-- `prefix` is a Lean keyword → field named `evArgs`.
-- Three paths: base (idx=nargs), fast (trivial domain), eval (evaluate+recurse).
-- Termination on (origArgs.length - idx).
--
-- Models ALL failure modes from C:
-- 1. mergeEnv can fail → skip result (C: bindings_builder_merge_or_clone, line 8498)
-- 2. extendBinder can fail → skip result (C: bind_domain_binder_builder, line 8506)
-- 3. isEmptyOrError && changed → error short-circuit (C: line 8498)
-- Failed results produce [] (skipped), matching C's `continue`.

import Mettapedia.Languages.MeTTa.HE.NondeterminismCarrier

/-!
# Direct Recursive Typed Ordinary Application

Formalizes `interpret_function_args` (eval.c:8440-8529) including all
failure modes: merge failure, binder extension failure, error short-circuit.

## C Seam Mapping

| Lean | C (eval.c) |
|------|-----------|
| `mergeEnv` returning `none` | `bindings_builder_merge_or_clone` returning false (line 8498) |
| `extendBinder` returning `none` | `bind_domain_binder_builder` returning false (line 8506) |
| `flatMap` returning `[]` | C's `continue` (skip result) |
| Error short-circuit | `atom_is_empty_or_error && !atom_eq` (line 8498) |
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## State -/

structure TypedApplyState where
  headAtom  : Atom
  origArgs  : List Atom
  argTypes  : List Atom
  idx       : Nat
  evArgs    : List Atom
  env       : Bindings
  deriving Repr

namespace TypedApplyState

def WellFormed (st : TypedApplyState) : Prop :=
  st.evArgs.length = st.idx ∧
  st.origArgs.length = st.argTypes.length ∧
  st.idx ≤ st.origArgs.length

def remaining (st : TypedApplyState) : Nat :=
  st.origArgs.length - st.idx

def initial (head : Atom) (args types : List Atom) (env : Bindings) :
    TypedApplyState :=
  { headAtom := head, origArgs := args, argTypes := types,
    idx := 0, evArgs := [], env := env }

theorem initial_wellFormed (head : Atom) (args types : List Atom) (env : Bindings)
    (h : args.length = types.length) :
    (initial head args types env).WellFormed :=
  ⟨rfl, h, Nat.zero_le _⟩

end TypedApplyState

/-! ## Direct Recursive Evaluation -/

/-- Direct recursive typed ordinary application.

    Parameters model the exact C interfaces:
    - `eval1 boundArg argType env` → result list (C: metta_eval_bind_typed_on_stack)
    - `applyEnv env atom` → substituted atom (C: bindings_apply)
    - `mergeEnv currentEnv evalResultEnv` → merged env or failure
      (C: bindings_builder_merge_or_clone, returns false on failure)
    - `extendBinder env argType argVal` → extended env or failure
      (C: bind_domain_binder_builder, returns false on failure)
    - `isTrivial argType` → true if type is Atom or similar (C: atom_is_symbol_id) -/
def typedApplyDirect
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (st : TypedApplyState) : ResultList :=
  if h : st.idx ≥ st.origArgs.length then
    -- BASE: reconstruct call term
    [(.expression (st.headAtom :: st.evArgs), st.env)]
  else
    have h_lt : st.idx < st.origArgs.length := Nat.lt_of_not_le h
    let origArg := st.origArgs[st.idx]
    let argType := if h' : st.idx < st.argTypes.length
                   then st.argTypes[st.idx]
                   else Atom.undefinedType
    let boundArg := applyEnv st.env origArg
    if isTrivial argType || origArg.isVariable then
      -- FAST PATH: skip evaluation
      -- C: bind_domain_binder_builder can fail (line 8466)
      match extendBinder st.env argType boundArg with
      | none => []  -- binder extension failed → no results (C: return)
      | some env' =>
        typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial
          { st with idx := st.idx + 1, evArgs := st.evArgs ++ [boundArg], env := env' }
    else
      -- EVAL PATH: evaluate argument, process each result
      let argResults := eval1 boundArg argType st.env
      argResults.flatMap fun (argVal, evalEnv) =>
        -- Step 1: merge eval result env with current env
        -- C: bindings_builder_merge_or_clone (line 8498)
        match mergeEnv st.env evalEnv with
        | none => []  -- merge failed → skip result (C: continue)
        | some mergedEnv =>
          -- Step 2: check error short-circuit
          -- C: atom_is_empty_or_error(arg_atom) && !atom_eq(arg_atom, orig_arg)
          if isEmptyOrError argVal && decide (argVal ≠ origArg) then
            [(argVal, mergedEnv)]  -- error propagates immediately
          else
            -- Step 3: extend binder for dependent types
            -- C: bind_domain_binder_builder (line 8506)
            match extendBinder mergedEnv argType argVal with
            | none => []  -- binder failed → skip result (C: no recurse)
            | some extEnv =>
              -- Step 4: recurse with advanced state
              typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial
                { st with idx := st.idx + 1,
                           evArgs := st.evArgs ++ [argVal],
                           env := extEnv }
termination_by st.origArgs.length - st.idx

/-! ## Invariants -/

/-- Base case: when idx ≥ nargs, result is exactly one call term. -/
theorem base_case (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (st : TypedApplyState) (h : st.idx ≥ st.origArgs.length) :
    typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st =
      [(.expression (st.headAtom :: st.evArgs), st.env)] := by
  unfold typedApplyDirect; simp [h]

/-- Zero-arg application produces `(head)` immediately. -/
theorem zero_args (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (head : Atom) (env : Bindings) :
    typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial
      (.initial head [] [] env) =
      [(.expression [head], env)] := by
  unfold typedApplyDirect; simp [TypedApplyState.initial]

/-! ## Examples -/

section Examples

-- Always-succeeding helpers (for basic tests)
private def idEval : Atom → Atom → Bindings → ResultList
  | a, _, b => [(a, b)]
private def idApply : Bindings → Atom → Atom := fun _ a => a
private def okMerge : Bindings → Bindings → Option Bindings
  | _, b => some b
private def okExtend : Bindings → Atom → Atom → Option Bindings
  | b, _, _ => some b
private def noTrivial : Atom → Bool := fun _ => false

/-- Single arg, all succeed: produces one call term. -/
example : typedApplyDirect idEval idApply okMerge okExtend noTrivial
    (.initial (.symbol "f") [.symbol "x"] [.symbol "T"] Bindings.empty) =
    [(.expression [.symbol "f", .symbol "x"], Bindings.empty)] := by
  unfold typedApplyDirect
  simp [TypedApplyState.initial, idEval, idApply, okMerge, okExtend, noTrivial,
        Atom.isVariable, isEmptyOrError, isEmptyAtom, isErrorAtom]
  unfold typedApplyDirect; simp

/-- Zero args: immediately produces `(f)`. -/
example : typedApplyDirect idEval idApply okMerge okExtend noTrivial
    (.initial (.symbol "f") [] [] Bindings.empty) =
    [(.expression [.symbol "f"], Bindings.empty)] :=
  zero_args _ _ _ _ _ _ _

-- Failing helpers (for failure tests)
private def failMerge : Bindings → Bindings → Option Bindings
  | _, _ => none
private def failExtend : Bindings → Atom → Atom → Option Bindings
  | _, _, _ => none

/-- Merge failure: eval produces results but merge fails → empty output. -/
example : typedApplyDirect idEval idApply failMerge okExtend noTrivial
    (.initial (.symbol "f") [.symbol "x"] [.symbol "T"] Bindings.empty) =
    [] := by
  unfold typedApplyDirect
  simp [TypedApplyState.initial, idEval, idApply, failMerge, noTrivial,
        Atom.isVariable]

/-- Binder extension failure: merge succeeds but extend fails → empty. -/
example : typedApplyDirect idEval idApply okMerge failExtend noTrivial
    (.initial (.symbol "f") [.symbol "x"] [.symbol "T"] Bindings.empty) =
    [] := by
  unfold typedApplyDirect
  simp [TypedApplyState.initial, idEval, idApply, okMerge, failExtend, noTrivial,
        Atom.isVariable, isEmptyOrError, isEmptyAtom, isErrorAtom]

/-- Fast path with binder failure: even trivial args can fail. -/
private def allTrivial : Atom → Bool := fun _ => true

example : typedApplyDirect idEval idApply okMerge failExtend allTrivial
    (.initial (.symbol "f") [.symbol "x"] [.symbol "T"] Bindings.empty) =
    [] := by
  unfold typedApplyDirect
  simp [TypedApplyState.initial, failExtend, allTrivial, Atom.isVariable]

/-- Error short-circuit: eval returns error, merge succeeds → error propagates. -/
private def errEval : Atom → Atom → Bindings → ResultList
  | _, _, b => [(Atom.empty, b)]

example : typedApplyDirect errEval idApply okMerge okExtend noTrivial
    (.initial (.symbol "f") [.symbol "x"] [.symbol "T"] Bindings.empty) =
    [(.symbol "Empty", Bindings.empty)] := by
  unfold typedApplyDirect
  simp [TypedApplyState.initial, errEval, okMerge, noTrivial,
        Atom.isVariable, Atom.empty, isEmptyOrError, isEmptyAtom, isErrorAtom]

end Examples

end Mettapedia.Languages.MeTTa.HE
