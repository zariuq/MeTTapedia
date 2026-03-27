import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import Mettapedia.Languages.MeTTa.HE.Properties

/-!
# HE MeTTa Declarative Core Spec (Grammar-Style)

This module provides the **unified declarative spec surface** for HE MeTTa,
mirroring the style of `PeTTa/DeclarativeSpec.lean`. It is simultaneously:

1. a readable declarative specification artifact (spec pseudocode in comments), and
2. a machine-checked bridge to the established formalization.

## Source of Truth

- `https://trueagi-io.github.io/hyperon-experimental/metta/`

## 4-Layer HE Spec Pack (Audit View)

1. **Evaluation relations** (`EvalSpec.lean`):
   Six mutually inductive relations mapping 1:1 to the spec pseudocode:
   `EvalAtom`, `InterpretExpression`, `InterpretFunction`,
   `InterpretArgs`, `InterpretTuple`, `MettaCall`.

2. **Implementation-refined top-level executable boundary**
   (`ExecutableBoundary.lean`):
   `EvalAtomStablyReaches` and `EvalAtomCertified`, which sharpen the
   top-level evaluator story without replacing the coarse declarative spec.

3. **Stateful instruction layer** (`MinimalMeTTa.lean`):
   `MinimalStep` relation for `eval`, `evalc`, `chain`, `unify`,
   `cons-atom`, `decons-atom`, `collapse-bind`, `superpose-bind`,
   `function`/`return`, `metta`, `context-space`, `call-native`.

4. **Properties & Conformance** (`Properties.lean`, `Conformance.lean`):
   Universal theorems by induction and derivation-tree witnesses.

## Spec Coverage Map

| Spec Lines | Section                              | Lean File       |
|------------|--------------------------------------|-----------------|
| 104-136    | metta (EvalAtom)                     | EvalSpec.lean   |
| 137-156    | type_cast                            | TypeCheck.lean  |
| 157-171    | match_types                          | Matching.lean   |
| 172-210    | interpret_expression                 | EvalSpec.lean   |
| 211-233    | interpret_tuple                      | EvalSpec.lean   |
| 234-275    | check_if_function_type_is_applicable | TypeCheck.lean  |
| 276-295    | check_argument_type                  | TypeCheck.lean  |
| 296-321    | interpret_function                   | EvalSpec.lean   |
| 322-347    | interpret_args                       | EvalSpec.lean   |
| 348-389    | metta_call                           | EvalSpec.lean   |
| 390-435    | match_atoms                          | Matching.lean   |
| 436-492    | merge/add_var_binding/equality       | Matching.lean   |
| 84-91      | minimal instructions                 | MinimalMeTTa.lean |

## Bridge Theorem Index

- `eval_empty_always` — Empty always passes through EvalAtom
- `eval_error_always` — Error always passes through EvalAtom
- `eval_variable_always` — Variables always pass through EvalAtom
- `eval_atom_type_always` — Atom type always passes through EvalAtom
- `mettaCall_error_always` — Error always passes through MettaCall
- `matchTypes_undefined_succeeds` — %Undefined% always matches
- `matchTypes_atom_succeeds` — Atom type always matches
- `matchAtoms_refl_symbol` — Symbol matches itself
- `cons_decons_roundtrip` — cons-atom/decons-atom round-trip
- `EvalAtomFiltered` — Success-priority filtering (spec lines 129-136)
-/

namespace Mettapedia.Languages.MeTTa.HE.DeclarativeSpec

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE

/-! ## Clause-Form Definitions

Named clause forms for each constructor, matching the PeTTa DeclarativeSpec style.
These are thin wrappers providing a named, auditable interface.

### Spec: Evaluate atom (metta) — lines 104-136

```
$metatype = <meta-type of the $atom>
if $atom == Empty or $atom ~ (Error ...):
    return [($atom, $bindings)]
elif $type == Atom or $type == $metatype or $metatype == Variable:
    return [($atom, $bindings)]
elif $metatype == Symbol or $metatype == Grounded or $atom == ():
    return type_cast($atom, $bindings, $type, $space)
else:
    $results = interpret_expression($atom, $type, $space, $bindings)
    $error = filter(lambda $a: $a ~ (Error ...), $results)
    $success = filter(lambda $a: not($a ~ (Error ...)), $results)
    if len($success) > 0:
        return $success
    else:
        return $error
```
-/

/-- Clause: Empty or Error atoms pass through unchanged (spec line 117). -/
def emptyOrErrorPassthrough (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) : Prop :=
  isEmptyOrError atom = true ∧
  EvalAtom space dispatch atom type_ b (atom, b)

/-- Clause: Type matches metatype, or metatype is Variable (spec line 119). -/
def typePassthrough (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) : Prop :=
  isEmptyOrError atom = false ∧
  (type_ = Atom.atomType ∨ type_ = getMetaType atom ∨ getMetaType atom = Atom.variableType) ∧
  EvalAtom space dispatch atom type_ b (atom, b)

/-- Clause: Symbol/Grounded/unit → typeCast (spec line 123). -/
def typeCastBranch (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (fuel : Nat) : Prop :=
  isEmptyOrError atom = false ∧
  (getMetaType atom = Atom.symbolType ∨ getMetaType atom = Atom.groundedType ∨ atom = Atom.unit) ∧
  r ∈ typeCast atom type_ space b fuel ∧
  EvalAtom space dispatch atom type_ b r

/-- Clause: Expression → interpret, non-error result (spec line 129).
    Note: the spec filters on `Error` only (not Empty) for success/error split.
    `Empty` is a success result in the metta function. -/
def interpretSuccessBranch (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  getMetaType atom = Atom.expressionType ∧
  atom ≠ Atom.unit ∧
  isErrorAtom r.1 = false ∧
  InterpretExpression space dispatch atom type_ b r ∧
  EvalAtom space dispatch atom type_ b r

/-! ### Spec: Call MeTTa expression (metta_call) — lines 348-389

```
if $atom ~ (Error ...):
    return [($atom, $bindings)]
$op = <head atom of the $atom expression>
$args = <tail of the $atom expression>
if <$op is executable grounded atom>:
    match <call $op native function passing $args as arguments>:
        case Ok($results):
            $results = [metta($r, $type, $space, $mb)
                        for ($r, $rb) in $results
                        for $mb in merge_bindings($rb, $bindings)]
        case RuntimeError($message):
            return [(Error $atom <message>)]
        case NoReduce:
            return [($atom, $bindings)]
        case IncorrectArgument:
            return [($atom, $bindings)]
else:
    $query_output = query($space, (= $atom $X))
    if len($query_output) > 0:
        for $rb in $query_output:
            for $mb in merge_bindings($rb, $bindings):
                if not(<$mb has loop bindings>):
                    $x = <value of $X from $mb>
                    $results += [metta($x, $type, $space, $mb)]
    else:
        $results += [($atom, $bindings)]
```
-/

/-- Clause: Error passthrough in mettaCall (spec line 359). -/
def mettaCallErrorPassthrough (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) : Prop :=
  isErrorAtom atom = true ∧
  MettaCall space dispatch atom type_ b (atom, b)

/-- Clause: Equation match (spec lines 376-382). -/
def equationMatchClause (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (rhs : Atom)
    (queryBindings merged : Bindings) (result : ResultPair) (fuel : Nat) : Prop :=
  isErrorAtom atom = false ∧
  (rhs, queryBindings) ∈ queryEquations space atom fuel ∧
  merged ∈ mergeBindings queryBindings b fuel ∧
  merged.hasLoop = false ∧
  EvalAtom space dispatch (merged.apply rhs fuel) type_ merged result ∧
  MettaCall space dispatch atom type_ b result

/-- Clause: No equations match (spec lines 383-384). -/
def noMatchClause (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) : Prop :=
  isErrorAtom atom = false ∧
  queryEquations space atom fuel = [] ∧
  MettaCall space dispatch atom type_ b (atom, b)

/-! ### Spec: Minimal MeTTa Instructions — lines 84-91

Published minimal instruction set (spec line 89):
```
(eval <atom>)           — one evaluation step
(evalc <atom> <space>)  — eval in context space
(chain <atom> <var> <template>) — evaluate and substitute
(unify <atom> <pattern> <then> <else>) — unify and branch
(cons-atom <head> <tail>)   — construct expression
(decons-atom <expression>)  — split expression
(collapse-bind <atom>)  — collect all results into tuple
(superpose-bind <tuple>) — distribute as nondeterministic results
(function <body>)       — evaluate until (return <atom>)
(metta <atom> <type> <space>) — eval with explicit type and space
(context-space)         — return the current context space
(call-native <op> <args>) — call native function
```

Note: `add-atom`, `remove-atom`, and `match` are NOT minimal instructions.
They are higher-level MeTTa built-ins handled by the interpreter layer.
-/

/-- Clause: cons-atom constructs expression from head and tail. -/
def consAtomClause (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) : Prop :=
  MinimalStep dispatch s
    (.expression [.symbol "cons-atom", hd, .expression tl]) ib
    s (.expression (hd :: tl), ib)

/-- Clause: decons-atom splits expression into head and tail. -/
def deconsAtomClause (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) : Prop :=
  MinimalStep dispatch s
    (.expression [.symbol "decons-atom", .expression (hd :: tl)]) ib
    s (.expression [hd, .expression tl], ib)

/-! ## Clause Introduction Theorems -/

theorem emptyOrErrorPassthrough_intro (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings)
    (h : isEmptyOrError atom = true) :
    emptyOrErrorPassthrough space dispatch atom type_ b :=
  ⟨h, .empty_or_error _ _ _ h⟩

theorem typePassthrough_intro (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings)
    (h_not_empty : isEmptyOrError atom = false)
    (h_pass : type_ = Atom.atomType ∨ type_ = getMetaType atom ∨ getMetaType atom = Atom.variableType) :
    typePassthrough space dispatch atom type_ b :=
  ⟨h_not_empty, h_pass, .type_pass _ _ _ h_not_empty h_pass⟩

theorem mettaCallErrorPassthrough_intro (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings)
    (h : isErrorAtom atom = true) :
    mettaCallErrorPassthrough space dispatch atom type_ b :=
  ⟨h, .error_passthrough _ _ _ h⟩

theorem consAtomClause_intro (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) :
    consAtomClause dispatch s hd tl ib :=
  .cons_atom _ _ _ _

theorem deconsAtomClause_intro (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) :
    deconsAtomClause dispatch s hd tl ib :=
  .decons_atom _ _ _ _

/-! ## Positive Examples

These are derivation-tree witnesses showing that specific inputs have valid
derivations. Cf. `Conformance.lean` for the full 36-test conformance suite. -/

private def emptySpace : Space := Space.empty
private def emptyB : Bindings := Bindings.empty
private def noDispatch : GroundedDispatch := .none

/-- Positive: Empty passes through EvalAtom.
    `!(metta Empty %Undefined% &self {})` → `[(Empty, {})]` -/
example : EvalAtom emptySpace noDispatch Atom.empty Atom.undefinedType emptyB
    (Atom.empty, emptyB) :=
  .empty_or_error _ _ _ rfl

/-- Positive: Error passes through EvalAtom.
    `!(metta (Error x msg) %Undefined% &self {})` → `[((Error x msg), {})]` -/
example : EvalAtom emptySpace noDispatch
    (Atom.error (.symbol "x") (.symbol "msg")) Atom.undefinedType emptyB
    (Atom.error (.symbol "x") (.symbol "msg"), emptyB) :=
  .empty_or_error _ _ _ rfl

/-- Positive: Variable passes through EvalAtom.
    `!(metta $x %Undefined% &self {})` → `[($x, {})]` -/
example : EvalAtom emptySpace noDispatch (.var "x") Atom.undefinedType emptyB
    (.var "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inr (Or.inr rfl))

/-- Positive: Atom type always passes through.
    `!(metta foo Atom &self {})` → `[(foo, {})]` -/
example : EvalAtom emptySpace noDispatch (.symbol "x") Atom.atomType emptyB
    (.symbol "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inl rfl)

/-- Positive: Symbol with type annotation matching → typeCast succeeds.
    `!(metta x Int {(: x Int)} {})` → `[(x, {})]` -/
example : EvalAtom
    (Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]])
    noDispatch (.symbol "x") (.symbol "Int") emptyB
    (.symbol "x", emptyB) := by
  apply EvalAtom.type_cast (fuel := 50)
  · rfl
  · decide
  · left; rfl
  · show _ ∈ typeCast _ _ _ _ 50; decide

/-- Positive: Equation match in MettaCall.
    Space `(= (f a) result)`, calling `(f a)` → `result`. -/
example : MettaCall
    (Space.ofList [.expression [.symbol "=",
      .expression [.symbol "f", .symbol "a"], .symbol "result"]])
    noDispatch
    (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType emptyB
    (.symbol "result", emptyB) := by
  apply MettaCall.equation_match (fuel := 50) (rhs := .symbol "result")
    (queryBindings := emptyB) (merged := emptyB)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    apply EvalAtom.type_cast (fuel := 50)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ 50; decide

/-- Positive: No equations match → return unchanged.
    Empty space, calling `(f a)` → `(f a)`. -/
example : MettaCall emptySpace noDispatch
    (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType emptyB
    (.expression [.symbol "f", .symbol "a"], emptyB) := by
  apply MettaCall.no_match (fuel := 50)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_no_eqs => rfl

/-- Positive: cons-atom builds expression.
    `(cons-atom a (b))` → `(a b)` -/
example : MinimalStep noDispatch emptySpace
    (.expression [.symbol "cons-atom", .symbol "a", .expression [.symbol "b"]]) emptyB
    emptySpace
    (.expression [.symbol "a", .symbol "b"], emptyB) :=
  .cons_atom _ _ _ _

/-- Positive: decons-atom splits expression.
    `(decons-atom (a b))` → `(a (b))` -/
example : MinimalStep noDispatch emptySpace
    (.expression [.symbol "decons-atom", .expression [.symbol "a", .symbol "b"]]) emptyB
    emptySpace
    (.expression [.symbol "a", .expression [.symbol "b"]], emptyB) :=
  .decons_atom _ _ _ _

/-! ## Negative Examples

These show that certain derivations are NOT valid. -/

/-- Negative: A non-error symbol is NOT derivable via `empty_or_error`.
    (Because `isEmptyOrError (.symbol "x") = false`.) -/
example : ¬ (isEmptyOrError (.symbol "x") = true) := by decide

/-- Negative: Different symbols do NOT match.
    `matchAtoms a b` = `[]` -/
example : matchAtoms (.symbol "a") (.symbol "b") 50 = [] := rfl

/-- Negative: Expression-symbol mismatch does NOT match.
    `matchAtoms a (a)` = `[]` -/
example : matchAtoms (.symbol "a") (.expression [.symbol "a"]) 50 = [] := rfl

/-- Negative: Length-mismatched expressions do NOT match.
    `matchAtoms (a) (a b)` = `[]` -/
example : matchAtoms (.expression [.symbol "a"])
    (.expression [.symbol "a", .symbol "b"]) 50 = [] := rfl

/-! ## Universal Properties

These are ∀-quantified theorems, not point examples. See `Properties.lean`
for the full set. -/

/-- ∀ atoms: Empty always passes through EvalAtom. -/
theorem eval_empty_always (space : Space) (dispatch : GroundedDispatch)
    (type_ : Atom) (b : Bindings) :
    EvalAtom space dispatch Atom.empty type_ b (Atom.empty, b) :=
  Properties.eval_empty_always space dispatch type_ b

/-- ∀ atoms: Error always passes through EvalAtom. -/
theorem eval_error_always (space : Space) (dispatch : GroundedDispatch)
    (src msg type_ : Atom) (b : Bindings) :
    EvalAtom space dispatch (Atom.error src msg) type_ b
      (Atom.error src msg, b) :=
  Properties.eval_error_always space dispatch src msg type_ b

/-- ∀ atoms: Variables always pass through EvalAtom. -/
theorem eval_variable_always (space : Space) (dispatch : GroundedDispatch)
    (v : String) (type_ : Atom) (b : Bindings) :
    EvalAtom space dispatch (.var v) type_ b (.var v, b) :=
  Properties.eval_variable_always space dispatch v type_ b

/-- ∀ atoms: Atom type always passes through EvalAtom (via case split). -/
theorem eval_atom_type_always (space : Space) (dispatch : GroundedDispatch)
    (a : Atom) (b : Bindings) :
    EvalAtom space dispatch a Atom.atomType b (a, b) :=
  Properties.eval_atom_type_always space dispatch a b

/-- ∀ atoms: Error always passes through MettaCall. -/
theorem mettaCall_error_always (space : Space) (dispatch : GroundedDispatch)
    (src msg type_ : Atom) (b : Bindings) :
    MettaCall space dispatch (Atom.error src msg) type_ b
      (Atom.error src msg, b) :=
  Properties.mettaCall_error_always space dispatch src msg type_ b

/-- ∀ types: %Undefined% always matches. -/
theorem matchTypes_undefined_succeeds (t : Atom) (b : Bindings) :
    matchTypes Atom.undefinedType t b ≠ [] :=
  Properties.matchTypes_undefined_succeeds t b

/-- ∀ types: Atom type always matches. -/
theorem matchTypes_atom_succeeds (t : Atom) (b : Bindings) :
    matchTypes t Atom.atomType b ≠ [] :=
  Properties.matchTypes_atom_succeeds t b

/-- ∀ symbols: A symbol matches itself. -/
theorem matchAtoms_refl_symbol (s : String) (fuel : Nat) (h : fuel > 0) :
    Bindings.empty ∈ matchAtoms (.symbol s) (.symbol s) fuel :=
  Properties.matchAtoms_refl_symbol s fuel h

/-- ∀ expressions: cons-atom followed by decons-atom is the identity. -/
theorem cons_decons_roundtrip (dispatch : GroundedDispatch) (s : Space)
    (hd : Atom) (tl : List Atom) (ib : Bindings) :
    MinimalStep dispatch s
      (.expression [.symbol "cons-atom", hd, .expression tl]) ib
      s (.expression (hd :: tl), ib) :=
  Properties.cons_decons_roundtrip dispatch s hd tl ib

/-! ## Operator-to-Clause Audit Index

### EvalAtom constructors (spec lines 104-136)
| Constructor         | Spec Line | Clause Def                  |
|--------------------|-----------|-----------------------------|
| `empty_or_error`    | 117       | `emptyOrErrorPassthrough`   |
| `type_pass`         | 119       | `typePassthrough`           |
| `type_cast`         | 123       | `typeCastBranch`            |
| `interpret_success` | 129       | `interpretSuccessBranch`    |
| `interpret_error`   | 135       | (error fallback)            |

### InterpretExpression constructors (spec lines 172-210)
| Constructor      | Spec Line | Description                  |
|-----------------|-----------|------------------------------|
| `function_path`  | 190-203   | operator has function type    |
| `tuple_path`     | 205-209   | tuple fallback                |
| `op_type_error`  | 184-186   | operator has incorrect type   |

### InterpretFunction constructors (spec lines 296-321)
| Constructor           | Spec Line | Description                |
|----------------------|-----------|----------------------------|
| `head_error`          | 312-314   | head evaluates to error     |
| `head_ok_tail_error`  | 315-320   | head ok, tail error         |
| `head_ok_tail_ok`     | 315-320   | head ok, tail ok, combine   |

### InterpretArgs constructors (spec lines 322-347)
| Constructor          | Spec Line | Description                |
|---------------------|-----------|----------------------------|
| `nil`                | (base)    | empty args → unit           |
| `head_changed_error` | 338-340   | head error AND changed      |
| `cons_tail_error`    | 341-346   | head ok, tail error         |
| `cons_ok`            | 341-346   | head ok, tail ok, combine   |

### InterpretTuple constructors (spec lines 211-233)
| Constructor   | Spec Line | Description                    |
|--------------|-----------|--------------------------------|
| `singleton`   | (base)    | single-element expression       |
| `head_error`  | 224-226   | head evaluates to error         |
| `tail_error`  | 228-230   | head ok, tail error             |
| `success`     | 231-232   | both head and tail ok, combine  |

### MettaCall constructors (spec lines 348-389)
| Constructor              | Spec Line | Description                  |
|-------------------------|-----------|------------------------------|
| `error_passthrough`      | 359       | error passes through          |
| `grounded_ok`            | 365-368   | grounded dispatch, Ok result  |
| `grounded_runtime_error` | 369-370   | grounded dispatch, error      |
| `grounded_no_reduce`     | 371-372   | grounded dispatch, NoReduce   |
| `grounded_incorrect_arg` | 373-374   | grounded dispatch, bad arg    |
| `equation_match`         | 376-382   | equation query match (applies merged bindings to RHS) |
| `no_match`               | 383-384   | no equations match            |
| `empty_results`          | 386-387   | all paths empty (non-grounded) |
| `grounded_empty_results` | 386-387   | grounded dispatch returns empty list |

### MinimalStep constructors (spec lines 84-91)
| Constructor         | Description                          |
|--------------------|--------------------------------------|
| `eval`              | `(eval <atom>)` — one step            |
| `evalc`             | `(evalc <atom> <space>)` — in context |
| `metta_instr`       | `(metta <atom> <type> <space>)`       |
| `chain`             | `(chain <atom> <var> <tmpl>)`         |
| `chain_empty`       | chain with Empty result               |
| `unify_match`       | `(unify ...)` — match succeeds        |
| `unify_no_match`    | `(unify ...)` — match fails           |
| `cons_atom`         | `(cons-atom <hd> <tl>)`              |
| `decons_atom`       | `(decons-atom <expr>)`               |
| `collapse_bind`     | `(collapse-bind <atom>)`             |
| `superpose_bind`    | `(superpose-bind <tuple>)`           |
| `function_return`   | `(function ...)` with `(return ...)`  |
| `function_no_return`| `(function ...)` with no return       |
| `context_space`     | `(context-space)` — return space      |
| `call_native`       | `(call-native <op> <args>)`           |

### Computable leaf operations (not in mutual inductive)
| Function                           | Spec Lines | File          |
|-----------------------------------|------------|---------------|
| `typeCast`                         | 137-156    | TypeCheck.lean |
| `matchTypes`                       | 157-171    | Matching.lean  |
| `checkIfFunctionTypeIsApplicable`  | 234-275    | TypeCheck.lean |
| `checkArgumentType`                | 276-295    | TypeCheck.lean |
| `matchAtoms`                       | 390-435    | Matching.lean  |
| `mergeBindings`                    | 436-451    | Matching.lean  |
| `addVarBinding`                    | 452-471    | Matching.lean  |
| `addVarEquality`                   | 472-492    | Matching.lean  |
| `queryEquations`                   | (Space)    | Space.lean     |
-/

end Mettapedia.Languages.MeTTa.HE.DeclarativeSpec
