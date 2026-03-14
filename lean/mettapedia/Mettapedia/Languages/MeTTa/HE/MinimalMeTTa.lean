import Mettapedia.Languages.MeTTa.HE.EvalSpec

/-!
# HE MeTTa Minimal Instructions (Stateful Operations)

Declarative specification of the minimal MeTTa instructions that involve
space mutation or control flow. These are the "assembly language" of MeTTa
(spec lines 84-91).

## Source of Truth
- `https://trueagi-io.github.io/hyperon-experimental/metta/` lines 84-91
- `https://trueagi-io.github.io/hyperon-experimental/minimal-metta/`

## Architecture
The 6 core evaluation functions (EvalSpec.lean) are PURE — they read the
space but don't modify it. Space mutation and control flow happen here.

Each constructor of `MinimalStep` takes a pre-state space and produces a
post-state space, making state changes explicit.

## Instruction Coverage
The published minimal instruction set (spec line 89) is exactly:
  eval, evalc, chain, unify, decons-atom, cons-atom, function, return,
  collapse-bind, superpose-bind, metta, context-space, call-native

Note: `add-atom`, `remove-atom`, and `match` are NOT in the minimal
instruction set. They are higher-level MeTTa built-ins handled by
the interpreter layer, not the minimal instruction machine.

## Bindings Threading
The minimal-metta spec defines interpreter state as a plan of
`(<atom>, <bindings>)` pairs. Each instruction receives input bindings
and produces output `(result_atom, result_bindings)` pairs.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Minimal MeTTa Instruction Step

Each constructor represents one minimal instruction and specifies its
effect on the space and the results it produces. -/

/-- A single minimal MeTTa instruction step.
    Parameters:
    - Pre-state space
    - Instruction atom
    - Input bindings (from the interpreter plan)
    - Post-state space
    - Result pair (atom, bindings) -/
inductive MinimalStep (dispatch : GroundedDispatch) :
    Space → Atom → Bindings → Space → ResultPair → Prop where

  /-- `(eval <atom>)` — One step of evaluation in current space.
      Spec: "makes one step of the evaluation".
      Space is unchanged (evaluation is pure). -/
  | eval (s : Space) (a : Atom) (ib : Bindings) (r : ResultPair)
      (h : EvalAtom s dispatch a Atom.undefinedType ib r) :
      MinimalStep dispatch s
        (.expression [.symbol "eval", a]) ib s r

  /-- `(evalc <atom> <context space>)` — One step in a different space.
      Spec: "makes one step of the evaluation in the context of the passed space".
      The context space is the second argument; current space is unchanged. -/
  | evalc (s ctxSpace : Space) (a : Atom) (ctxAtoms : List Atom) (ib : Bindings)
      (r : ResultPair)
      (h_ctx : ctxSpace = Space.ofList ctxAtoms)
      (h : EvalAtom ctxSpace dispatch a Atom.undefinedType ib r) :
      MinimalStep dispatch s
        (.expression [.symbol "evalc", a, .expression ctxAtoms]) ib s r

  /-- `(metta <atom> <type> <space>)` — Evaluate with explicit type and space.
      Spec: "evaluate <atom> in MeTTa interpreter using <space> as a context
      and expecting result with <type>". -/
  | metta_instr (s ctxSpace : Space) (a type_ : Atom)
      (ctxAtoms : List Atom) (ib : Bindings) (r : ResultPair)
      (h_ctx : ctxSpace = Space.ofList ctxAtoms)
      (h : EvalAtom ctxSpace dispatch a type_ ib r) :
      MinimalStep dispatch s
        (.expression [.symbol "metta", a, type_, .expression ctxAtoms]) ib s r

  /-- `(chain <atom> <var> <template>)` — Evaluate atom, substitute result
      into template.
      Spec: "interpret <atom> and substitute <var> in <template> by the
      result of the interpretation". -/
  | chain (s : Space) (a : Atom) (v : String) (template : Atom)
      (ib : Bindings) (evalResult : ResultPair)
      (h_eval : EvalAtom s dispatch a Atom.undefinedType ib evalResult)
      (h_not_empty : evalResult.1 ≠ Atom.empty) :
      MinimalStep dispatch s
        (.expression [.symbol "chain", a, .var v, template]) ib
        s ((evalResult.2.assign v evalResult.1).apply template, evalResult.2)

  /-- `(chain <atom> <var> <template>)` — Atom evaluates to Empty → return Empty. -/
  | chain_empty (s : Space) (a : Atom) (v : String) (template : Atom)
      (ib : Bindings) (rb : Bindings)
      (h_eval : EvalAtom s dispatch a Atom.undefinedType ib (Atom.empty, rb)) :
      MinimalStep dispatch s
        (.expression [.symbol "chain", a, .var v, template]) ib
        s (Atom.empty, rb)

  /-- `(unify <atom> <pattern> <then> <else>)` — Unify atom with pattern.
      Match succeeds → merge match bindings with input bindings, apply to `then`.
      Spec: "matches <atom> with <pattern>. If match is successful then it
      returns <then> atom and merges bindings of the original <atom> to
      resulting variable bindings." -/
  | unify_match (s : Space) (atom pattern thenBranch _elseBranch : Atom)
      (ib : Bindings) (matchBindings merged : Bindings) (fuel : Nat)
      (h_match : matchBindings ∈ matchAtoms atom pattern fuel)
      (h_merge : merged ∈ mergeBindings matchBindings ib fuel)
      (h_no_loop : merged.hasLoop = false) :
      MinimalStep dispatch s
        (.expression [.symbol "unify", atom, pattern, thenBranch, _elseBranch]) ib
        s (merged.apply thenBranch, merged)

  /-- `(unify <atom> <pattern> <then> <else>)` — Unify fails.
      Match fails → return `else` unchanged.
      Spec: "return <else> argument otherwise". -/
  | unify_no_match (s : Space) (atom pattern _thenBranch elseBranch : Atom)
      (ib : Bindings) (fuel : Nat)
      (h_no_match : matchAtoms atom pattern fuel = []) :
      MinimalStep dispatch s
        (.expression [.symbol "unify", atom, pattern, _thenBranch, elseBranch]) ib
        s (elseBranch, ib)

  /-- `(cons-atom <head> <tail>)` — Construct expression from head and tail.
      Spec: "return the expression constructed from <head> and <tail>". -/
  | cons_atom (s : Space) (hd : Atom) (tl : List Atom) (ib : Bindings) :
      MinimalStep dispatch s
        (.expression [.symbol "cons-atom", hd, .expression tl]) ib
        s (.expression (hd :: tl), ib)

  /-- `(decons-atom <expression>)` — Deconstruct expression into head and tail.
      Spec: "return the head and the tail of the passed expression". -/
  | decons_atom (s : Space) (hd : Atom) (tl : List Atom) (ib : Bindings) :
      MinimalStep dispatch s
        (.expression [.symbol "decons-atom", .expression (hd :: tl)]) ib
        s (.expression [hd, .expression tl], ib)

  /-- `(collapse-bind <atom>)` — Collect all evaluation results into a tuple.
      Spec: "evaluates <atom> and returns an expression which contains all
      alternative evaluations in a form `(<atom> <bindings>)`. `<bindings>`
      are represented in a form of a grounded atom."

      Modeling note: The spec represents bindings as opaque grounded atoms
      in the result expression. We model this via a `ResultSet` parameter
      carrying the full `(Atom × Bindings)` pairs, since `Bindings` cannot
      be faithfully embedded in `Atom` without an encoding function.
      The key semantic property is preserved: `superpose-bind` restores
      the exact `(atom, bindings)` pairs that `collapse-bind` collected. -/
  | collapse_bind (s : Space) (a : Atom) (ib : Bindings) (results : ResultSet)
      (h_results : ∀ r ∈ results,
        EvalAtom s dispatch a Atom.undefinedType ib r)
      (h_complete : ∀ r : ResultPair,
        EvalAtom s dispatch a Atom.undefinedType ib r → r ∈ results) :
      MinimalStep dispatch s
        (.expression [.symbol "collapse-bind", a]) ib
        s (.expression (results.map Prod.fst), ib)

  /-- `(superpose-bind ((<atom> <bindings>) ...))` — Distribute results as
      nondeterministic outcomes.
      Spec: "puts list of the results into the interpreter plan each pair
      as a separate alternative."
      Each `(atom, bindings)` pair from the collapsed results becomes a
      separate derivation, restoring the bindings that were active when
      that particular result was produced.

      The `results` parameter must be the same `ResultSet` produced by the
      corresponding `collapse-bind`. This is the key invariant linking the
      two instructions — the `results` carry both atoms AND their bindings. -/
  | superpose_bind (s : Space) (results : ResultSet) (r : ResultPair)
      (ib : Bindings) (h_mem : r ∈ results) :
      MinimalStep dispatch s
        (.expression [.symbol "superpose-bind", .expression (results.map Prod.fst)]) ib
        s r

  /-- `(function <body>)` / `(return <atom>)` — Evaluate body until return.
      Spec: "evaluate <body> until (return <atom>) is evaluated".
      The body evaluates to `(return x)` → the instruction returns `x`. -/
  | function_return (s : Space) (body returnAtom : Atom) (ib rb : Bindings)
      (h_eval : EvalAtom s dispatch body Atom.undefinedType ib
        (.expression [.symbol "return", returnAtom], rb)) :
      MinimalStep dispatch s
        (.expression [.symbol "function", body]) ib
        s (returnAtom, rb)

  /-- `(function <body>)` — Body does NOT return → error.
      Spec: "NoReturn error". -/
  | function_no_return (s : Space) (body result : Atom) (ib rb : Bindings)
      (h_eval : EvalAtom s dispatch body Atom.undefinedType ib (result, rb))
      (h_not_return : ∀ x, result ≠ .expression [.symbol "return", x]) :
      MinimalStep dispatch s
        (.expression [.symbol "function", body]) ib
        s (Atom.error (.expression [.symbol "function", body])
            (.symbol "NoReturn"), rb)

  /-- `(context-space)` — Return the current space.
      Spec: "return the space which is used by the interpreter". -/
  | context_space (s : Space) (ib : Bindings) :
      MinimalStep dispatch s
        (.expression [.symbol "context-space"]) ib
        s (.expression s.atoms, ib)

  /-- `(call-native <function name> <pointer> <arguments>)` — Call native function.
      Spec: "call the passed Rust function with the passed arguments".
      Modeled via `GroundedDispatch.execute` since native functions are opaque. -/
  | call_native (s : Space) (op : Atom) (args : List Atom) (ib : Bindings)
      (nativeResults : ResultSet) (r : ResultPair)
      (merged : Bindings) (finalResult : ResultPair) (fuel : Nat)
      (h_exec : dispatch.isExecutable op = true)
      (h_native : dispatch.execute op args = .ok nativeResults)
      (h_mem : r ∈ nativeResults)
      (h_merge : merged ∈ mergeBindings r.2 ib fuel)
      (h_recurse : EvalAtom s dispatch r.1 Atom.undefinedType merged finalResult) :
      MinimalStep dispatch s
        (.expression [.symbol "call-native", op, .expression args]) ib
        s finalResult

/-! ## Multi-Step Evaluation

A program is a sequence of atoms (spec line 94). Each atom either:
- Gets added to the space (if not prefixed with `!`)
- Gets evaluated and its result returned (if prefixed with `!`)

This captures the stateful evolution of the space across a program. -/

/-- Multi-step execution: reflexive transitive closure of minimal steps. -/
inductive MinimalSteps (dispatch : GroundedDispatch) :
    Space → List (Atom × Bindings) → Space → List ResultPair → Prop where
  /-- No more instructions. -/
  | nil (s : Space) :
      MinimalSteps dispatch s [] s []
  /-- Execute one instruction, then continue. -/
  | cons (s₁ s₂ s₃ : Space) (instr : Atom) (ib : Bindings)
      (rest : List (Atom × Bindings))
      (r : ResultPair) (rs : List ResultPair)
      (h_step : MinimalStep dispatch s₁ instr ib s₂ r)
      (h_rest : MinimalSteps dispatch s₂ rest s₃ rs) :
      MinimalSteps dispatch s₁ ((instr, ib) :: rest) s₃ (r :: rs)

end Mettapedia.Languages.MeTTa.HE
