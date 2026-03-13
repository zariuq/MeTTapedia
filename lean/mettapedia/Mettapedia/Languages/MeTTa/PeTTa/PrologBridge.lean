import Mettapedia.Logic.Prolog.Prolog
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Bridge: PeTTa Evaluation ↔ Prolog Oracle

This file wires the abstract `EvalOracle` (from `Logic.Prolog.Eval`) to the
concrete `PeTTaEval` relation (from `OSLF.PeTTa.Eval`), producing the
**MeTTa Prolog oracle** that instantiates `reduceCall` with PeTTa semantics.

## Architecture

```
EvalOracle (abstract)          ← Logic.Prolog.Eval
  ↑ instantiated by
MeTTaPrologOracle (s)          ← this file
  ↑ used in
PrologEval oracle goal env r   ← Logic.Prolog.Eval.PrologEval
  ↑ correctness via
compileExpr_correct             ← OSLF.PeTTa.TranslateExpr
```

## Key Result

`meTTaPrologOracle_correct` states that for the MeTTa oracle:
`oracle.call [e] outs ↔ PeTTaEval s e outs`

This is the semantic contract that `translate_expr` relies on: `reduce([e], Out)` in
Prolog is equivalent to evaluating `e` in MeTTa.

## References

- PeTTa `translator.pl`: `reduce/2`, `eval/2`
- PeTTa `metta.pl`: `eval(C, Out) :- translate_expr(C, Goals, Out), call_goals(Goals).`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Logic.Prolog

/-! ## Space Adapter -/

/-- Adapt a `PeTTaSpace` to the abstract `PrologSpace` interface.

    The `matchFacts` operation queries the PeTTa space for all stored atoms
    matching `pat`, returning those atoms themselves (not the template
    instantiations). This corresponds to PeTTa's `'get-atoms'(&self)` followed
    by pattern matching. -/
def peTTaSpaceAdapter (s : PeTTaSpace) : PrologSpace where
  matchFacts pat := s.storedAtoms.filter (fun atom => (matchPattern pat atom).length > 0)

/-! ## MeTTa Prolog Oracle -/

/-- The MeTTa Prolog oracle: wires `reduceCall` to `PeTTaEval` and
    `spaceMatch` to `PeTTaSpace.spaceMatch`.

    `oracle.call args outs` holds iff:
    - `args = [e]` (a single expression), and
    - `PeTTaEval s e outs` holds (PeTTa evaluation produces `outs`).

    `oracle.matchEval pat tmpl outs` holds iff:
    - `outs = s.spaceMatch pat tmpl` (the instantiated template answers).

    The oracle is `Prop`-valued (not computable), keeping the formalization
    kernel-checkable. -/
def meTTaPrologOracle (s : PeTTaSpace) : EvalOracle where
  space := peTTaSpaceAdapter s
  call  := fun args outs =>
    match args with
    | [e] => PeTTaEval s e outs
    | _   => False
  matchEval := fun pat tmpl outs => outs = s.spaceMatch pat tmpl

/-! ## Basic Properties -/

/-- The MeTTa oracle correctly dispatches single-expression calls to PeTTaEval. -/
theorem meTTaOracle_call_single (s : PeTTaSpace) (e : Pattern) (outs : List Pattern) :
    (meTTaPrologOracle s).call [e] outs ↔ PeTTaEval s e outs := by
  simp [meTTaPrologOracle]

/-- Multi-argument oracle calls always fail (only single expressions are supported). -/
theorem meTTaOracle_call_non_single (s : PeTTaSpace) (args : List Pattern) (outs : List Pattern)
    (h : args.length ≠ 1) : ¬ (meTTaPrologOracle s).call args outs := by
  simp [meTTaPrologOracle]
  match args with
  | []     => simp
  | [_]    => simp at h
  | _ :: _ :: _ => simp

/-- The space adapter's `matchFacts` returns exactly the stored atoms that match `pat`. -/
theorem peTTaSpaceAdapter_matchFacts (s : PeTTaSpace) (pat : Pattern) :
    (peTTaSpaceAdapter s).matchFacts pat =
    s.storedAtoms.filter (fun atom => (matchPattern pat atom).length > 0) := rfl

/-- The MeTTa oracle's `matchEval` correctly dispatches to `PeTTaSpace.spaceMatch`. -/
theorem meTTaOracle_matchEval (s : PeTTaSpace) (pat tmpl : Pattern) (outs : List Pattern) :
    (meTTaPrologOracle s).matchEval pat tmpl outs ↔ outs = s.spaceMatch pat tmpl := by
  simp [meTTaPrologOracle]

/-! ## Prolog-PeTTaEval Connection -/

/-- A `PrologEval` derivation under the MeTTa oracle for `reduceCall [e]`
    witnesses a `PeTTaEval` derivation for `e`.

    The result environments have "Out" bound to each PeTTaEval answer. -/
theorem reduceCall_meTTa_sound (s : PeTTaSpace) (e : Pattern) (env : PEnv)
    (r : PrologEvalResult)
    (h : PrologEval (meTTaPrologOracle s) (.reduceCall [e]) env r) :
    ∃ outs : List Pattern,
      PeTTaEval s e outs ∧
      r.answers = outs.map (fun out => env.insert "Out" out) := by
  cases h with
  | reduceCall_eval _ _ outs' h_oracle =>
    exact ⟨outs', (meTTaOracle_call_single s e outs').mp h_oracle, rfl⟩

/-- Converse: lift a `PeTTaEval` derivation to a `PrologEval` `reduceCall`. -/
theorem pettaEval_to_reduceCall (s : PeTTaSpace) (e : Pattern) (env : PEnv)
    (outs : List Pattern) (h : PeTTaEval s e outs) :
    PrologEval (meTTaPrologOracle s) (.reduceCall [e]) env
      (.normal (outs.map (fun out => env.insert "Out" out))) :=
  PrologEval.reduceCall_eval [e] env outs
    ((meTTaOracle_call_single s e outs).mpr h)

end Mettapedia.Languages.MeTTa.PeTTa
