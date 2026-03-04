import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval

/-!
# Grounded Oracle Layer for PeTTa Evaluation

This file formalizes the **grounded atom execution model** as an abstract oracle.

## Motivation

MeTTa allows atoms whose evaluation is delegated to the host language (Rust, SWI Prolog, etc.).
These are called *grounded atoms* and their execution is treated as a black box from the
perspective of the pure MeTTa evaluator.

Rather than modeling Rust/SWI FFI directly (which would be out-of-scope for a pure Lean
formalization), we use a **`Prop`-valued oracle abstraction** that:

1. Keeps the pure formalization kernel-checkable.
2. Allows concrete implementations (`metta-il-rust`, SWI PeTTa) to supply the oracle instance
   as a separate trust boundary.
3. Theorems about `MeTTaEvalG oracle ...` are universally quantified over any oracle satisfying
   the stated contracts — matching the "oracle" pattern in `Computability/OracleTM.lean`.

## Architecture

```
PeTTaEval       (pure, type-free, no oracle)            ← Eval.lean
MeTTaEval       (binding-threading, error-propagation)  ← MeTTaEval.lean
MeTTaEvalG      (+ grounded dispatch via oracle)        ← this file (GroundedOracle.lean)
```

`MeTTaEvalG oracle s p ty bindings results` extends `MeTTaEval` with three constructors:
- `liftPure`: lifts any `MeTTaEval` derivation unchanged
- `groundedCall`: calls a grounded function via the oracle (returns results)
- `groundedNoReduce`: a grounded function call with no oracle results passes through

## Oracle Contract

`GroundedOracle` is a `Prop`-valued structure with three fields:
- `isExecutable : String → Prop` — whether `f` is a grounded function name
- `call : String → List Pattern → List Pattern → Prop` — the call relation
- `call_total : ∀ f args, isExecutable f → ∃ results, call f args results` — totality

## References

- MeTTa spec §grounded: `trueagi-io.github.io/hyperon-experimental/metta/`
  (`interpret_function`, grounded atom execution)
- PeTTa transpiler: `hyperon/PeTTa/transpiler.pl`
- `MeTTaEval`: `Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! ## The Grounded Oracle -/

/-- An abstract oracle for grounded function execution.

    `GroundedOracle` abstracts over the host-language execution semantics.
    A concrete implementation (Rust, SWI Prolog, etc.) provides:
    - which function names are "executable" (backed by a host implementation)
    - the call relation: (f, args) ↦ results
    - a totality guarantee: executable functions always return *some* result list

    The oracle is `Prop`-valued (not `def`), keeping the formalization kernel-checkable.
    Concrete oracle instances live outside this file (separate trust boundary). -/
structure GroundedOracle where
  /-- Whether a symbol names an executable grounded function. -/
  isExecutable : String → Prop
  /-- The call relation: `call f args results` means calling grounded function `f`
      with evaluated arguments `args` produces result patterns `results`.
      May be multivalued (nondeterministic grounded functions). -/
  call : String → List Pattern → List Pattern → Prop
  /-- Totality: every executable function returns *some* result (possibly empty).
      Ensures either a successful call or a no-reduce case is always reachable. -/
  call_total : ∀ f args, isExecutable f → ∃ results, call f args results

/-! ## Argument Evaluation: InterpretArgs -/

/-- Sequential argument evaluation, threading bindings.

    `InterpretArgs s bindings rawArgs evaledArgs finalBindings` means:
    starting from `bindings`, evaluating each pattern in `rawArgs` in the atomspace `s`
    produces the head values `evaledArgs` and final output bindings `finalBindings`.

    This formalizes the MeTTa spec's `interpret_args` predicate:
    each argument is evaluated left-to-right; the first available answer is selected
    and bindings are threaded through.

    **Design note**: we take the FIRST answer for each argument (using `hfirst`),
    matching PeTTa's deterministic single-answer argument-evaluation strategy.
    For full nondeterminism, one would branch over all answers; this is future work. -/
inductive InterpretArgs (s : PeTTaSpace) :
    Bindings → List Pattern → List Pattern → Bindings → Prop where
  /-- Base case: no arguments → no evaluated results, bindings unchanged. -/
  | nil (bindings : Bindings) :
      InterpretArgs s bindings [] [] bindings

  /-- Inductive case: evaluate the head argument `a`, take the first answer `aVal`,
      then continue evaluating `rest` from the resulting bindings. -/
  | cons (bindings : Bindings) (a : Pattern) (rest : List Pattern)
      (ty : Pattern)
      (aResults : EvalResult) (aVal : Pattern) (aBindings : Bindings)
      (restEvals : List Pattern) (finalBindings : Bindings)
      -- Evaluate the head argument with the current bindings
      (ha : MeTTaEval s a ty bindings aResults)
      -- Pick the first result
      (hfirst : (aVal, aBindings) ∈ aResults)
      -- Continue with remaining arguments from the new bindings
      (hrest : InterpretArgs s aBindings rest restEvals finalBindings) :
      InterpretArgs s bindings (a :: rest) (aVal :: restEvals) finalBindings

/-! ## Basic lemmas about InterpretArgs -/

/-- Nil args evaluate trivially. -/
@[simp]
theorem interpretArgs_nil (s : PeTTaSpace) (bindings : Bindings) :
    InterpretArgs s bindings [] [] bindings :=
  InterpretArgs.nil bindings

/-- For nil raw args, the evaluated args are nil and bindings unchanged. -/
theorem interpretArgs_nil_iff (s : PeTTaSpace) (bindings : Bindings)
    (evaledArgs : List Pattern) (finalBindings : Bindings) :
    InterpretArgs s bindings [] evaledArgs finalBindings ↔
    evaledArgs = [] ∧ finalBindings = bindings := by
  constructor
  · intro h
    cases h with
    | nil => exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact InterpretArgs.nil _

/-- The length of evaluated args equals the length of raw args. -/
theorem interpretArgs_length {s : PeTTaSpace} {bindings : Bindings}
    {rawArgs evaledArgs : List Pattern} {finalBindings : Bindings}
    (h : InterpretArgs s bindings rawArgs evaledArgs finalBindings) :
    rawArgs.length = evaledArgs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih]

/-! ## Extended Evaluation with Grounded Dispatch -/

/-- **Extended MeTTa evaluation with grounded function dispatch**.

    `MeTTaEvalG oracle s p ty bindings results` extends `MeTTaEval` with:

    1. **`liftPure`**: lifts any `MeTTaEval` derivation unchanged.
    2. **`groundedCall`**: dispatches to a grounded function via the oracle.
    3. **`groundedNoReduce`**: a grounded function call that produces no results
       passes through as the unreduced application.

    The oracle provides the `isExecutable` / `call` semantics.

    **Oracle precedence**: when `oracle.isExecutable f`, the grounded dispatch takes
    priority over rule-based reduction (mirroring PeTTa's `check_grounded/1` predicate
    which returns grounded results before trying rewrite rules). -/
inductive MeTTaEvalG (oracle : GroundedOracle) (s : PeTTaSpace) :
    Pattern → Pattern → Bindings → EvalResult → Prop where

  /-- **Lift**: any `MeTTaEval` derivation is also a `MeTTaEvalG` derivation.
      The grounded oracle adds new constructors on top of the pure evaluator. -/
  | liftPure (p ty : Pattern) (bindings : Bindings) (results : EvalResult)
      (h : MeTTaEval s p ty bindings results) :
      MeTTaEvalG oracle s p ty bindings results

  /-- **Grounded dispatch**: `(f a₁ … aₙ)` where `f` is an executable grounded symbol.

      Steps:
      1. Evaluate each argument via `InterpretArgs`
      2. Call the oracle with the evaluated arguments
      3. Return each result paired with the final output bindings

      This formalizes `interpret_function` for grounded atoms in the MeTTa spec. -/
  | groundedCall (f : String) (rawArgs : List Pattern)
      (ty : Pattern) (bindings finalBindings : Bindings)
      (evaledArgs : List Pattern) (results : List Pattern)
      -- f is executable (backed by the oracle)
      (hexec : oracle.isExecutable f)
      -- Evaluate the arguments sequentially
      (hargs : InterpretArgs s bindings rawArgs evaledArgs finalBindings)
      -- Call the oracle
      (hcall : oracle.call f evaledArgs results) :
      MeTTaEvalG oracle s (.apply f rawArgs) ty bindings
        (results.map (·, finalBindings))

  /-- **No-reduce pass-through**: `f` is executable but the oracle returns no results.
      In this case, the application is returned unchanged (it does not reduce).

      This models the MeTTa spec's `NotReducible` case for grounded functions. -/
  | groundedNoReduce (f : String) (rawArgs : List Pattern)
      (ty : Pattern) (bindings finalBindings : Bindings)
      (evaledArgs : List Pattern)
      -- f is executable
      (hexec : oracle.isExecutable f)
      -- Arguments are evaluated
      (hargs : InterpretArgs s bindings rawArgs evaledArgs finalBindings)
      -- The oracle produces no results
      (hcall : oracle.call f evaledArgs []) :
      MeTTaEvalG oracle s (.apply f rawArgs) ty bindings
        [(.apply f evaledArgs, finalBindings)]

/-! ## Basic Properties -/

/-- The empty oracle: no symbols are executable. -/
def emptyOracle : GroundedOracle where
  isExecutable := fun _ => False
  call         := fun _ _ _ => False
  call_total   := fun _ _ h => h.elim

/-- For the empty oracle, `MeTTaEvalG` coincides with `MeTTaEval`. -/
theorem meTTaEvalG_empty_oracle_iff {s : PeTTaSpace} {p ty : Pattern}
    {bindings : Bindings} {results : EvalResult}
    (h : MeTTaEvalG emptyOracle s p ty bindings results) :
    MeTTaEval s p ty bindings results := by
  cases h with
  | liftPure _ _ _ _ hpure => exact hpure
  | groundedCall _ _ _ _ _ _ _ hexec _ _ => exact hexec.elim
  | groundedNoReduce _ _ _ _ _ _ hexec _ _ => exact hexec.elim

/-- Every `MeTTaEval` derivation lifts to any `MeTTaEvalG`. -/
theorem meTTaEval_to_meTTaEvalG {oracle : GroundedOracle} {s : PeTTaSpace}
    {p ty : Pattern} {bindings : Bindings} {results : EvalResult}
    (h : MeTTaEval s p ty bindings results) :
    MeTTaEvalG oracle s p ty bindings results :=
  MeTTaEvalG.liftPure p ty bindings results h

/-! ## Grounded Oracle Correctness -/

/-- For any oracle, `groundedCall` is directly constructible from its hypotheses. -/
theorem meTTaEvalG_groundedCall_mk {oracle : GroundedOracle} {s : PeTTaSpace}
    {f : String} {rawArgs : List Pattern} {ty : Pattern}
    {bindings finalBindings : Bindings}
    {evaledArgs : List Pattern} {results : List Pattern}
    (hexec : oracle.isExecutable f)
    (hargs : InterpretArgs s bindings rawArgs evaledArgs finalBindings)
    (hcall : oracle.call f evaledArgs results) :
    MeTTaEvalG oracle s (.apply f rawArgs) ty bindings
      (results.map (·, finalBindings)) :=
  MeTTaEvalG.groundedCall f rawArgs ty bindings finalBindings
    evaledArgs results hexec hargs hcall

/-- The oracle's `call_total` guarantees that every executable function has a derivation
    in `MeTTaEvalG` (either a `groundedCall` or `groundedNoReduce`).

    This is the existence theorem: grounded dispatch always produces *some* result. -/
theorem meTTaEvalG_executable_total {oracle : GroundedOracle} {s : PeTTaSpace}
    {f : String} (hexec : oracle.isExecutable f)
    (rawArgs : List Pattern) (ty : Pattern)
    (bindings finalBindings : Bindings) (evaledArgs : List Pattern)
    (hargs : InterpretArgs s bindings rawArgs evaledArgs finalBindings) :
    ∃ results, MeTTaEvalG oracle s (.apply f rawArgs) ty bindings results := by
  obtain ⟨res, hcall⟩ := oracle.call_total f evaledArgs hexec
  cases res with
  | nil =>
    exact ⟨[(.apply f evaledArgs, finalBindings)],
      MeTTaEvalG.groundedNoReduce f rawArgs ty bindings finalBindings evaledArgs
        hexec hargs hcall⟩
  | cons r rs =>
    exact ⟨(r :: rs).map (·, finalBindings),
      MeTTaEvalG.groundedCall f rawArgs ty bindings finalBindings evaledArgs
        (r :: rs) hexec hargs hcall⟩

/-- `groundedNoReduce` result is always a singleton containing the unreduced application. -/
theorem meTTaEvalG_groundedNoReduce_result {oracle : GroundedOracle} {s : PeTTaSpace}
    {f : String} {rawArgs : List Pattern} {ty : Pattern}
    {bindings finalBindings : Bindings} {evaledArgs : List Pattern}
    (hexec : oracle.isExecutable f)
    (hargs : InterpretArgs s bindings rawArgs evaledArgs finalBindings)
    (hcall : oracle.call f evaledArgs []) :
    MeTTaEvalG oracle s (.apply f rawArgs) ty bindings
      [(.apply f evaledArgs, finalBindings)] :=
  MeTTaEvalG.groundedNoReduce f rawArgs ty bindings finalBindings evaledArgs
    hexec hargs hcall

/-! ## Oracle Composition -/

/-- The **union oracle** combines two oracles: a symbol is executable if it is
    executable in either oracle, and calls dispatch to whichever oracle handles it. -/
def GroundedOracle.union (o₁ o₂ : GroundedOracle) : GroundedOracle where
  isExecutable f := o₁.isExecutable f ∨ o₂.isExecutable f
  call f args results := o₁.call f args results ∨ o₂.call f args results
  call_total f args h := by
    rcases h with h₁ | h₂
    · obtain ⟨results, hcall⟩ := o₁.call_total f args h₁
      exact ⟨results, Or.inl hcall⟩
    · obtain ⟨results, hcall⟩ := o₂.call_total f args h₂
      exact ⟨results, Or.inr hcall⟩

/-- Oracle union is commutative for `isExecutable`. -/
theorem GroundedOracle.union_executable_comm (o₁ o₂ : GroundedOracle) (f : String) :
    (o₁.union o₂).isExecutable f ↔ (o₂.union o₁).isExecutable f := by
  simp [GroundedOracle.union, or_comm]

end Mettapedia.Languages.MeTTa.PeTTa
