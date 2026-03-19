import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import MeTTailCore.Crypto.SHA256

/-!
# HE Runtime Contract

Rust-facing behavioral contract for HE MeTTa operations, derived from the
computable spec (MinimalMeTTa.lean + EvalSpec.lean).

## What This Is

For each HE op that Rust may execute, this artifact exports:
1. **Entry classification** — head, lane, arity, argument roles
2. **Input shape** — argument types, scope/binding expectations
3. **Behavioral contract** — result shapes, error cases, determinism
4. **Semantic authority** — which Lean functions are the source of truth
5. **Conformance fixtures** — positive and negative examples

## What This Is Not

- NOT a serialization of the evaluator internals
- NOT a replacement for the contract pipeline (scope contract, native profile)
- NOT derived from the deprecated Datalog/Ascent layer

## Source of Truth

- `MinimalMeTTa.lean` — 13 minimal instructions (bug-fixed)
- `Space.lean` — queryEquations, getAtomTypes, simpleMatch
- `Matching.lean` — matchAtoms, mergeBindings
- `TypeCheck.lean` — typeCast, checkIfFunctionTypeIsApplicable
- `Types.lean` — Bindings, ResultSet, Bindings.toAtom round-trip
-/

namespace Mettapedia.Languages.MeTTa.HE.RuntimeContract

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE

/-! ## Contract Schema -/

/-- Whether an operation may produce multiple results. -/
inductive Determinism where
  | deterministic
  | nondeterministic
  | branchingTwoWay
deriving Repr, DecidableEq

/-- How bindings flow through an operation. -/
inductive BindingsFlow where
  /-- Output bindings = input bindings (no binding changes). -/
  | passthrough
  /-- Output bindings are merged from match/unification result + input. -/
  | mergeFromMatch
  /-- Output bindings gain a new variable assignment. -/
  | assignVariable
  /-- Output bindings come from each collected result (restored by superpose-bind). -/
  | restoreFromCollapse
  /-- No binding change, but the collected expression encodes bindings via toAtom. -/
  | encodeBindings
deriving Repr, DecidableEq

/-- A single conformance fixture: concrete input → expected output. -/
structure ConformanceFixture where
  /-- Human-readable label. -/
  label : String
  /-- Whether this is a positive (expected behavior) or negative (error/edge) case. -/
  positive : Bool
  /-- The instruction atom. -/
  instructionAtom : String
  /-- Input bindings (as assignment list). -/
  inputBindings : List (String × String)
  /-- Expected result atom(s). -/
  expectedResults : List String
  /-- Expected output bindings (as assignment list), if deterministic. -/
  expectedBindings : Option (List (String × String))
deriving Repr

/-- Runtime contract for a single HE operation. -/
structure OpRuntimeContract where
  /-- Operation head name. -/
  head : String
  /-- Number of arguments (excluding head). -/
  arity : Nat
  /-- Argument role descriptions (positional). -/
  argRoles : List String
  /-- Which MinimalMeTTa constructor(s) define this op. -/
  specConstructors : List String
  /-- Which computable Lean functions are the semantic authority. -/
  semanticAuthority : List String
  /-- Result determinism. -/
  determinism : Determinism
  /-- How bindings flow through this operation. -/
  bindingsFlow : BindingsFlow
  /-- Possible result shapes. -/
  resultCases : List String
  /-- Possible error conditions. -/
  errorCases : List String
  /-- Whether this operation mutates the space. -/
  mutatesSpace : Bool
  /-- Conformance fixtures. -/
  fixtures : List ConformanceFixture
deriving Repr

/-- The full HE runtime contract artifact. -/
structure HERuntimeContractArtifact where
  dialect : String
  schemaVersion : Nat
  contracts : List OpRuntimeContract
deriving Repr

/-! ## Vertical Slice: match, unify, chain, case -/

def matchContract : OpRuntimeContract where
  head := "match"
  arity := 3
  argRoles := ["space-ref", "pattern", "template"]
  specConstructors :=
    [ "MinimalStep.match"       -- HELanguageDef: MC_Match
    , "MinimalStep.match_empty" -- HELanguageDef: MC_Match_Empty
    ]
  semanticAuthority :=
    [ "Space.queryEquations"    -- equation lookup
    , "Matching.matchAtoms"     -- bidirectional unification
    , "Matching.mergeBindings"  -- binding merge
    , "Bindings.apply"          -- template substitution
    ]
  determinism := .nondeterministic
  bindingsFlow := .mergeFromMatch
  resultCases :=
    [ "match succeeds: template with pattern variables substituted, one result per match"
    , "no match: Empty atom"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "match: simple equation lookup"
        positive := true
        instructionAtom := "(match &self (= a $x) $x)"
        inputBindings := []
        expectedResults := ["b"]
        expectedBindings := some [("x", "b")]
      }
    , { label := "match: no equation → Empty"
        positive := true
        instructionAtom := "(match &self (= z $x) $x)"
        inputBindings := []
        expectedResults := ["Empty"]
        expectedBindings := none
      }
    , { label := "match: multiple results (nondeterministic)"
        positive := true
        instructionAtom := "(match &self (= color $x) $x)"
        inputBindings := []
        expectedResults := ["red", "green"]
        expectedBindings := none
      }
    ]

def unifyContract : OpRuntimeContract where
  head := "unify"
  arity := 4
  argRoles := ["target-atom", "pattern", "success-body", "failure-body"]
  specConstructors :=
    [ "MinimalStep.unify_match"
    , "MinimalStep.unify_no_match"
    ]
  semanticAuthority :=
    [ "Matching.matchAtoms"
    , "Matching.mergeBindings"
    , "Bindings.hasLoop"
    , "Bindings.apply"
    ]
  determinism := .branchingTwoWay
  bindingsFlow := .mergeFromMatch
  resultCases :=
    [ "match succeeds: merged bindings applied to success-body"
    , "match fails: failure-body with original input bindings"
    ]
  errorCases :=
    [ "variable loop in merged bindings: filtered out (may yield no results)"
    ]
  mutatesSpace := false
  fixtures :=
    [ { label := "unify: match succeeds, binds variable"
        positive := true
        instructionAtom := "(unify (A B) ($x $y) (found $x $y) (not-found))"
        inputBindings := []
        expectedResults := ["(found A B)"]
        expectedBindings := some [("x", "A"), ("y", "B")]
      }
    , { label := "unify: no match, returns else branch"
        positive := true
        instructionAtom := "(unify (A B) (C D) success failure)"
        inputBindings := []
        expectedResults := ["failure"]
        expectedBindings := some []
      }
    , { label := "unify: variable loop filtered"
        positive := false
        instructionAtom := "(unify $x $y success failure)"
        inputBindings := []
        expectedResults := []
        expectedBindings := none
      }
    ]

def chainContract : OpRuntimeContract where
  head := "chain"
  arity := 3
  argRoles := ["atom-to-eval", "variable", "template"]
  specConstructors :=
    [ "MinimalStep.chain"
    , "MinimalStep.chain_empty"
    ]
  semanticAuthority :=
    [ "EvalAtom"           -- evaluates the atom
    , "Bindings.assign"    -- binds variable to result
    , "Bindings.apply"     -- substitutes in template
    ]
  determinism := .deterministic
  bindingsFlow := .assignVariable
  resultCases :=
    [ "eval succeeds (non-Empty): template with $var substituted, output bindings include $var assignment"
    , "eval yields Empty: return Empty, output bindings from eval (no $var assignment)"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "chain: eval result substituted into template"
        positive := true
        instructionAtom := "(chain x $v (tag $v))"
        inputBindings := []
        expectedResults := ["(tag x)"]
        expectedBindings := some [("v", "x")]
      }
    , { label := "chain: eval yields Empty → return Empty"
        positive := true
        instructionAtom := "(chain Empty $v (tag $v))"
        inputBindings := []
        expectedResults := ["Empty"]
        expectedBindings := some []
      }
    ]

/-- `switch` / `switch-minimal` — the primitive pattern-matching control op.
    Both surface names are accepted by parseSwitchMinimalCallArgs.
    Scrutinee is already evaluated; branches are `((pattern template) ...)`.
    First matching branch wins; on no match, returns Empty. -/
def switchContract : OpRuntimeContract where
  head := "switch"
  arity := 2
  argRoles := ["scrutinee (already evaluated)", "branches ((pattern template) ...)"]
  specConstructors :=
    [ "MC_SwitchMinimal_Start"
    , "MC_SwitchMinimal_Match"
    , "MC_SwitchMinimal_NoMatch"
    ]
  semanticAuthority :=
    [ "selectSwitchTemplate" -- iterate branches, first match wins
    , "Matching.matchAtoms"  -- pattern ↔ scrutinee unification
    , "Matching.mergeBindings"
    , "Bindings.hasLoop"     -- filter variable loops
    , "Bindings.apply"       -- substitute into template
    ]
  determinism := .nondeterministic
  bindingsFlow := .mergeFromMatch
  resultCases :=
    [ "first matching branch: template with pattern variables substituted (may yield multiple results if match is nondeterministic)"
    , "no matching branch: Empty"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "switch: first match wins"
        positive := true
        instructionAtom := "(switch a ((a ok) (b bad)))"
        inputBindings := []
        expectedResults := ["ok"]
        expectedBindings := some []
      }
    , { label := "switch: variable pattern binds into template"
        positive := true
        instructionAtom := "(switch z (($x (tag $x))))"
        inputBindings := []
        expectedResults := ["(tag z)"]
        expectedBindings := some [("x", "z")]
      }
    , { label := "switch: no match → Empty"
        positive := false
        instructionAtom := "(switch z ((a ok) (b bad)))"
        inputBindings := []
        expectedResults := ["Empty"]
        expectedBindings := none
      }
    , { label := "switch-minimal: identical to switch"
        positive := true
        instructionAtom := "(switch-minimal a ((a ok)))"
        inputBindings := []
        expectedResults := ["ok"]
        expectedBindings := some []
      }
    ]

/-- `case` — evaluates scrutinee, then delegates to switch.
    This is NOT a separate pattern-matching primitive. It compiles to:
    1. Evaluate scrutinee via metta(scrutinee, %Undefined%)
    2. Feed the result into switch(result, branches)
    The matching semantics are entirely in switch. -/
def caseContract : OpRuntimeContract where
  head := "case"
  arity := 2
  argRoles := ["scrutinee (to be evaluated)", "branches ((pattern template) ...)"]
  specConstructors :=
    [ "MC_Case_Start (evaluates scrutinee, then delegates to switch)"
    ]
  semanticAuthority :=
    [ "metta"                -- evaluates scrutinee
    , "switchContract"       -- delegates matching to switch
    ]
  determinism := .nondeterministic
  bindingsFlow := .mergeFromMatch
  resultCases :=
    [ "scrutinee evaluates, then matching branch selected (via switch semantics)"
    , "no matching branch: Empty"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "case: evaluates scrutinee then matches"
        positive := true
        instructionAtom := "(case a ((a ok) (b bad)))"
        inputBindings := []
        expectedResults := ["ok"]
        expectedBindings := some []
      }
    , { label := "case: no match → Empty"
        positive := false
        instructionAtom := "(case z ((a ok) (b bad)))"
        inputBindings := []
        expectedResults := ["Empty"]
        expectedBindings := none
      }
    ]

/-- `collapse-bind` — □ modality: collect ALL evaluation results with bindings.
    Evaluates atom, returns one expression containing all `(<result> <bindings.toAtom>)`
    pairs. The encoded bindings can be restored by superpose-bind via `Bindings.ofAtom?`.
    Round-trip guaranteed by `Bindings.ofAtom_toAtom`. -/
def collapseBindContract : OpRuntimeContract where
  head := "collapse-bind"
  arity := 1
  argRoles := ["atom (to evaluate and collect all results)"]
  specConstructors :=
    [ "MinimalStep.collapse_bind"
    ]
  semanticAuthority :=
    [ "EvalAtom"                -- evaluates the atom (all derivations)
    , "Bindings.toAtom"         -- encodes bindings into the result expression
    , "Bindings.ofAtom_toAtom"  -- round-trip proof (kernel-checked)
    ]
  determinism := .deterministic
  bindingsFlow := .encodeBindings
  resultCases :=
    [ "one or more results: expression of (<atom> <bindings.toAtom>) pairs"
    , "no results: empty expression ()"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "collapse-bind: single result with bindings encoded"
        positive := true
        instructionAtom := "(collapse-bind x)"
        inputBindings := []
        expectedResults := ["((x (Bindings () ())))"]
        expectedBindings := some []
      }
    , { label := "collapse-bind: empty eval → empty expression"
        positive := false
        instructionAtom := "(collapse-bind (match &self (= z $w) $w))"
        inputBindings := []
        expectedResults := ["()"]
        expectedBindings := some []
      }
    ]

/-- `superpose-bind` — ◇ modality: restore results from collapse-bind output.
    Takes an expression of `(<atom> <encoded-bindings>)` pairs and distributes
    each as a separate nondeterministic alternative, restoring the original bindings.
    Complement of collapse-bind. -/
def superposeBindContract : OpRuntimeContract where
  head := "superpose-bind"
  arity := 1
  argRoles := ["encoded-pairs (from collapse-bind output)"]
  specConstructors :=
    [ "MinimalStep.superpose_bind"
    ]
  semanticAuthority :=
    [ "Bindings.ofAtom?"        -- decodes bindings from encoded form
    , "Bindings.ofAtom_toAtom"  -- round-trip proof (kernel-checked)
    ]
  determinism := .nondeterministic
  bindingsFlow := .restoreFromCollapse
  resultCases :=
    [ "one result per encoded pair: original (atom, bindings) restored"
    , "empty input: no results"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "superpose-bind: restores single pair"
        positive := true
        instructionAtom := "(superpose-bind ((x (Bindings () ()))))"
        inputBindings := []
        expectedResults := ["x"]
        expectedBindings := some []
      }
    , { label := "superpose-bind: restores multiple pairs nondeterministically"
        positive := true
        instructionAtom := "(superpose-bind ((a (Bindings () ())) (b (Bindings ((v a)) ()))))"
        inputBindings := []
        expectedResults := ["a", "b"]
        expectedBindings := none
      }
    , { label := "superpose-bind: empty input → no results"
        positive := false
        instructionAtom := "(superpose-bind ())"
        inputBindings := []
        expectedResults := []
        expectedBindings := none
      }
    ]

/-- `assert` — evaluate expression, check if result matches True.
    On success: return unit `()`. On failure: return explicit Error atom.
    Ref: MC_Assert_Start, MC_Assert_True, MC_Assert_NotTrue. -/
def assertContract : OpRuntimeContract where
  head := "assert"
  arity := 1
  argRoles := ["expression (to evaluate and check against True)"]
  specConstructors :=
    [ "MC_Assert_Start"
    , "MC_Assert_True"
    , "MC_Assert_NotTrue"
    ]
  semanticAuthority :=
    [ "metta"                   -- evaluates the expression
    , "Matching.matchAtoms"     -- matches result against True
    , "Matching.mergeBindings"  -- merges match bindings
    , "Bindings.hasLoop"        -- filters variable loops
    ]
  determinism := .branchingTwoWay
  bindingsFlow := .mergeFromMatch
  resultCases :=
    [ "result matches True: return unit atom ()"
    , "result does not match True: return (Error (assert <expr>) (<result> not True))"
    ]
  errorCases :=
    [ "assertion failure: explicit Error atom with the failing result"
    ]
  mutatesSpace := false
  fixtures :=
    [ { label := "assert: True → unit"
        positive := true
        instructionAtom := "(assert True)"
        inputBindings := []
        expectedResults := ["()"]
        expectedBindings := some []
      }
    , { label := "assert: False → Error"
        positive := false
        instructionAtom := "(assert False)"
        inputBindings := []
        expectedResults := ["(Error (assert False) (False not True))"]
        expectedBindings := some []
      }
    , { label := "assert: non-boolean → Error"
        positive := false
        instructionAtom := "(assert hello)"
        inputBindings := []
        expectedResults := ["(Error (assert hello) (hello not True))"]
        expectedBindings := some []
      }
    ]

/-- `eval` — one step of evaluation in current space.
    Ref: MinimalMeTTa.lean eval constructor, metta.md "makes one step of the evaluation". -/
def evalContract : OpRuntimeContract where
  head := "eval"
  arity := 1
  argRoles := ["atom (to evaluate one step)"]
  specConstructors := ["MinimalStep.eval"]
  semanticAuthority :=
    [ "EvalAtom"  -- the 6-function evaluation loop
    ]
  determinism := .nondeterministic
  bindingsFlow := .mergeFromMatch
  resultCases :=
    [ "atom reduces: one or more result atoms with updated bindings"
    , "atom is irreducible: returned unchanged"
    ]
  errorCases :=
    [ "stack overflow (fuel exhaustion): atom returned unchanged"
    ]
  mutatesSpace := false
  fixtures :=
    [ { label := "eval: symbol is irreducible"
        positive := true
        instructionAtom := "(eval x)"
        inputBindings := []
        expectedResults := ["x"]
        expectedBindings := some []
      }
    , { label := "eval: expression with equation reduces"
        positive := true
        instructionAtom := "(eval (f a))"
        inputBindings := []
        expectedResults := ["b"]
        expectedBindings := none
      }
    ]

/-- `cons-atom` — construct an expression from head and tail.
    Pure structural operation, no evaluation, no binding changes. -/
def consAtomContract : OpRuntimeContract where
  head := "cons-atom"
  arity := 2
  argRoles := ["head (atom)", "tail (expression)"]
  specConstructors := ["MinimalStep.cons_atom"]
  semanticAuthority := []
  determinism := .deterministic
  bindingsFlow := .passthrough
  resultCases :=
    [ "always succeeds: expression with head prepended to tail elements"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "cons-atom: prepend to list"
        positive := true
        instructionAtom := "(cons-atom a (b c))"
        inputBindings := []
        expectedResults := ["(a b c)"]
        expectedBindings := some []
      }
    , { label := "cons-atom: prepend to empty"
        positive := true
        instructionAtom := "(cons-atom a ())"
        inputBindings := []
        expectedResults := ["(a)"]
        expectedBindings := some []
      }
    ]

/-- `decons-atom` — deconstruct an expression into head and tail.
    Pure structural operation. Requires a non-empty expression. -/
def deconsAtomContract : OpRuntimeContract where
  head := "decons-atom"
  arity := 1
  argRoles := ["expression (non-empty, to deconstruct)"]
  specConstructors := ["MinimalStep.decons_atom"]
  semanticAuthority := []
  determinism := .deterministic
  bindingsFlow := .passthrough
  resultCases :=
    [ "non-empty expression: returns (head tail) where tail is the remaining elements"
    ]
  errorCases :=
    [ "empty expression (): undefined (no MinimalStep constructor matches)"
    ]
  mutatesSpace := false
  fixtures :=
    [ { label := "decons-atom: split expression"
        positive := true
        instructionAtom := "(decons-atom (a b c))"
        inputBindings := []
        expectedResults := ["(a (b c))"]
        expectedBindings := some []
      }
    , { label := "decons-atom: singleton"
        positive := true
        instructionAtom := "(decons-atom (a))"
        inputBindings := []
        expectedResults := ["(a ())"]
        expectedBindings := some []
      }
    ]

/-- `function` / `return` — evaluate body in a loop until `(return <atom>)`.
    `function` is the loop wrapper; `return` is the exit signal.
    If the body never produces `(return ...)`, a NoReturn error is returned. -/
def functionContract : OpRuntimeContract where
  head := "function"
  arity := 1
  argRoles := ["body (to evaluate until return)"]
  specConstructors :=
    [ "MinimalStep.function_return"
    , "MinimalStep.function_no_return"
    ]
  semanticAuthority :=
    [ "EvalAtom"  -- evaluates body
    ]
  determinism := .deterministic
  bindingsFlow := .passthrough
  resultCases :=
    [ "body evaluates to (return <atom>): unwrap and return <atom>"
    , "body does not produce (return ...): return (Error (function <body>) NoReturn)"
    ]
  errorCases :=
    [ "NoReturn: body reached a terminal form that is not (return <atom>)"
    ]
  mutatesSpace := false
  fixtures :=
    [ { label := "function: return unwraps value"
        positive := true
        instructionAtom := "(function (return ok))"
        inputBindings := []
        expectedResults := ["ok"]
        expectedBindings := some []
      }
    , { label := "function: no return → NoReturn error"
        positive := false
        instructionAtom := "(function stuck)"
        inputBindings := []
        expectedResults := ["(Error (function stuck) NoReturn)"]
        expectedBindings := some []
      }
    ]

/-- `superpose` — nondeterministic branch over expression elements.
    Unlike superpose-bind, this does NOT encode/restore bindings.
    Each element of the input expression becomes a separate alternative. -/
def superposeContract : OpRuntimeContract where
  head := "superpose"
  arity := 1
  argRoles := ["expression (elements to branch over)"]
  specConstructors :=
    [ "MC_Superpose"
    , "MC_Superpose_Empty"
    ]
  semanticAuthority := []
  determinism := .nondeterministic
  bindingsFlow := .passthrough
  resultCases :=
    [ "non-empty expression: one result per element (nondeterministic)"
    , "empty expression (): return Empty"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "superpose: branch over elements"
        positive := true
        instructionAtom := "(superpose (a b c))"
        inputBindings := []
        expectedResults := ["a", "b", "c"]
        expectedBindings := none
      }
    , { label := "superpose: empty → Empty"
        positive := false
        instructionAtom := "(superpose ())"
        inputBindings := []
        expectedResults := ["Empty"]
        expectedBindings := some []
      }
    ]

/-- `context-space` — return the current atomspace as an expression.
    No arguments, no side effects. -/
def contextSpaceContract : OpRuntimeContract where
  head := "context-space"
  arity := 0
  argRoles := []
  specConstructors := ["MinimalStep.context_space"]
  semanticAuthority := ["Space.atoms"]
  determinism := .deterministic
  bindingsFlow := .passthrough
  resultCases :=
    [ "always succeeds: expression containing all atoms in the current space"
    ]
  errorCases := []
  mutatesSpace := false
  fixtures :=
    [ { label := "context-space: empty space"
        positive := true
        instructionAtom := "(context-space)"
        inputBindings := []
        expectedResults := ["()"]
        expectedBindings := some []
      }
    ]

/-- `call-native` — call a foreign (Rust) function with arguments.
    Spec note (minimal-metta.md lines 372-376): call-native currently cannot
    return bindings, so output bindings are the input bindings.
    The native function is dispatched via GroundedDispatch.execute. -/
def callNativeContract : OpRuntimeContract where
  head := "call-native"
  arity := 2
  argRoles := ["op (executable grounded atom)", "args (expression of arguments)"]
  specConstructors := ["MinimalStep.call_native"]
  semanticAuthority :=
    [ "GroundedDispatch.isExecutable"
    , "GroundedDispatch.execute"
    ]
  determinism := .nondeterministic
  bindingsFlow := .passthrough
  resultCases :=
    [ "native call succeeds: result atom from native, input bindings preserved"
    , "runtime error: Error atom"
    , "no reduce: atom returned unchanged"
    ]
  errorCases :=
    [ "GroundedResult.runtimeError: explicit error from native function"
    , "GroundedResult.incorrectArgument: wrong argument types"
    ]
  mutatesSpace := false
  fixtures :=
    [ { label := "call-native: bindings are not modified (spec limitation)"
        positive := true
        instructionAtom := "(call-native + (1 2))"
        inputBindings := [("x", "preserved")]
        expectedResults := ["3"]
        expectedBindings := some [("x", "preserved")]
      }
    ]

/-! ## Artifact Assembly -/

def heRuntimeContractArtifact : HERuntimeContractArtifact where
  dialect := "he"
  schemaVersion := 1
  contracts :=
    [ -- Core matching
      matchContract
    , unifyContract
    , switchContract
    , caseContract
    -- Binding threading
    , chainContract
    , collapseBindContract
    , superposeBindContract
    -- Control
    , assertContract
    , functionContract
    , superposeContract
    -- Evaluation entry points
    , evalContract
    -- Structural ops
    , consAtomContract
    , deconsAtomContract
    -- Runtime infrastructure
    , contextSpaceContract
    , callNativeContract
    ]

/-! ## JSON Rendering -/

private def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else acc.push c) ""

private def jsonStr (s : String) : String := s!"\"{jsonEscape s}\""
private def jsonBool (b : Bool) : String := if b then "true" else "false"
private def jsonNat (n : Nat) : String := s!"{n}"

private def jsonStrList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map jsonStr) ++ "]"

private def determinismToString : Determinism → String
  | .deterministic => "deterministic"
  | .nondeterministic => "nondeterministic"
  | .branchingTwoWay => "branchingTwoWay"

private def bindingsFlowToString : BindingsFlow → String
  | .passthrough => "passthrough"
  | .mergeFromMatch => "mergeFromMatch"
  | .assignVariable => "assignVariable"
  | .restoreFromCollapse => "restoreFromCollapse"
  | .encodeBindings => "encodeBindings"

private def jsonOptStrList : Option (List (String × String)) → String
  | none => "null"
  | some pairs =>
    let entries := pairs.map fun (k, v) => s!"{jsonStr k}: {jsonStr v}"
    "{" ++ String.intercalate ", " entries ++ "}"

private def renderFixture (f : ConformanceFixture) : String :=
  "      {"
    ++ s!" \"label\": {jsonStr f.label}"
    ++ s!", \"positive\": {jsonBool f.positive}"
    ++ s!", \"instructionAtom\": {jsonStr f.instructionAtom}"
    ++ s!", \"expectedResults\": {jsonStrList f.expectedResults}"
    ++ " }"

private def renderContract (c : OpRuntimeContract) : String :=
  let fixtureLines := String.intercalate ",\n" (c.fixtures.map renderFixture)
  "    {\n"
    ++ s!"      \"head\": {jsonStr c.head},\n"
    ++ s!"      \"arity\": {jsonNat c.arity},\n"
    ++ s!"      \"argRoles\": {jsonStrList c.argRoles},\n"
    ++ s!"      \"specConstructors\": {jsonStrList c.specConstructors},\n"
    ++ s!"      \"semanticAuthority\": {jsonStrList c.semanticAuthority},\n"
    ++ s!"      \"determinism\": {jsonStr (determinismToString c.determinism)},\n"
    ++ s!"      \"bindingsFlow\": {jsonStr (bindingsFlowToString c.bindingsFlow)},\n"
    ++ s!"      \"resultCases\": {jsonStrList c.resultCases},\n"
    ++ s!"      \"errorCases\": {jsonStrList c.errorCases},\n"
    ++ s!"      \"mutatesSpace\": {jsonBool c.mutatesSpace},\n"
    ++ s!"      \"fixtures\": [\n{fixtureLines}\n      ]\n"
    ++ "    }"

def HERuntimeContractArtifact.renderJson (a : HERuntimeContractArtifact) : String :=
  let contractLines := String.intercalate ",\n" (a.contracts.map renderContract)
  "{\n"
    ++ s!"  \"dialect\": {jsonStr a.dialect},\n"
    ++ s!"  \"schemaVersion\": {jsonNat a.schemaVersion},\n"
    ++ s!"  \"contracts\": [\n{contractLines}\n  ]\n"
    ++ "}"

def HERuntimeContractArtifact.checksumString (a : HERuntimeContractArtifact) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex a.renderJson

/-! ## Export / Check -/

def exportHeRuntimeContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heRuntimeContractArtifact
  let jsonPath := outDir / "he.runtime_contract.json"
  let checksumPath := outDir / "he.runtime_contract.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
  IO.println s!"exported he runtime contract to {outDir}"
  pure 0

def checkHeRuntimeContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heRuntimeContractArtifact
  let jsonPath := outDir / "he.runtime_contract.json"
  let checksumPath := outDir / "he.runtime_contract.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      IO.println s!"[ok] he runtime contract matches at {outDir}"
      pure 0
    else
      if !jsonOk then
        IO.println s!"[drift] he runtime contract json mismatch at {jsonPath}"
      if !checksumOk then
        IO.println s!"[drift] he runtime contract checksum mismatch at {checksumPath}"
      pure 3
  catch e =>
    IO.println s!"he runtime contract check failed: {e}"
    pure 2

section Canaries
#check @heRuntimeContractArtifact
#check @exportHeRuntimeContract
#check @checkHeRuntimeContract
end Canaries

end Mettapedia.Languages.MeTTa.HE.RuntimeContract
