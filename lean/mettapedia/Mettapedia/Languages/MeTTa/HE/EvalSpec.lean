import Mettapedia.Languages.MeTTa.HE.TypeCheck

/-!
# HE MeTTa Declarative Evaluation Specification

Mutual inductive relations for the 6 core evaluation functions of the
Hyperon Experimental MeTTa interpreter. Each constructor is a universally
quantified proposition mapping directly to a clause in the official spec.

## Source of Truth
- `https://trueagi-io.github.io/hyperon-experimental/metta/`

## Architecture
- **Layer 1** (computable leaves): `Types.lean`, `Space.lean`, `Matching.lean`, `TypeCheck.lean`
- **Layer 2** (this file): Declarative inductive relations — no fuel, no computation,
  pure `Prop`-valued. Nondeterminism = multiple valid derivation trees.
- **Layer 3** (downstream): `Conformance.lean` (derivation witnesses), `Properties.lean`
  (universal theorems by induction on derivations).

## Design
Each relation produces a single `ResultPair`. Multiple results from the spec's
pseudocode correspond to multiple valid derivation trees for the same input.
Result ordering (spec line 210: `$tuples + $errors`) is an implementation
detail, not captured here — the relation is order-free by construction.

The "already evaluated" marker (spec lines 121, 131-133) is an optimization
deferred to v2. Omitting it is conservative (allows more derivations).
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Core Evaluation Relations

Six mutually inductive relations corresponding to the six core evaluation
functions in the HE spec (lines 105-389). Each constructor cites the
spec lines it formalizes.

Parameters shared by all relations:
- `space : Space` — the context atomspace (read-only; space mutation is in MinimalMeTTa)
- `dispatch : GroundedDispatch` — grounded operation dispatch table

The computable leaf functions (`matchAtoms`, `mergeBindings`, `matchTypes`,
`typeCast`, `checkIfFunctionTypeIsApplicable`, `getAtomTypes`, `queryEquations`)
are referenced as hypotheses in constructors. -/

mutual

/-- Evaluate an atom to a single result.
    Ref: spec lines 105-136 "Evaluate atom (metta)".

    Input: atom, expected type, bindings.
    Output: one (result_atom, result_bindings) pair. -/
inductive EvalAtom (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → Prop where
  /-- Spec line 117-118: Empty or Error atoms pass through unchanged.
      ```
      if $atom == Empty or $atom ~ (Error ...):
          return [($atom, $bindings)]
      ``` -/
  | empty_or_error (atom type_ : Atom) (b : Bindings)
      (h : isEmptyOrError atom = true) :
      EvalAtom space dispatch atom type_ b (atom, b)
  /-- Spec line 119: Type matches meta-type, or meta-type is Variable.
      ```
      elif $type == Atom or $type == $metatype or $metatype == Variable:
          return [($atom, $bindings)]
      ``` -/
  | type_pass (atom type_ : Atom) (b : Bindings)
      (h_not_empty : isEmptyOrError atom = false)
      (h_pass : type_ = Atom.atomType
              ∨ type_ = getMetaType atom
              ∨ getMetaType atom = Atom.variableType) :
      EvalAtom space dispatch atom type_ b (atom, b)
  /-- Spec lines 123-124: Symbol, Grounded, or empty-expression → typeCast.
      ```
      elif $metatype == Symbol or $metatype == Grounded or $atom == ():
          return type_cast($atom, $bindings, $type, $space)
      ```
      One derivation per element of `typeCast`'s result list. -/
  | type_cast (atom type_ : Atom) (b : Bindings) (r : ResultPair) (fuel : Nat)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_cast_branch : getMetaType atom = Atom.symbolType
                     ∨ getMetaType atom = Atom.groundedType
                     ∨ atom = Atom.unit)
      (h_result : r ∈ typeCast atom type_ space b fuel) :
      EvalAtom space dispatch atom type_ b r
  /-- Spec lines 126-134: Expression → interpret, filter successes.
      ```
      $results = interpret_expression($atom, $type, $space, $bindings)
      $success = filter(not Error, $results)
      if len($success) > 0: return $success
      ```
      One derivation per successful (non-error) intermediate result. -/
  | interpret_success (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpression space dispatch atom type_ b r)
      (h_not_error : isErrorAtom r.1 = false) :
      EvalAtom space dispatch atom type_ b r
  /-- Spec lines 135-136: Interpret produces an error result.
      ```
      $error = filter(lambda $a: $a ~ (Error ...), $results)
      ...
      else: return $error
      ```
      Note: The spec filters ONLY on `Error`, not `Empty`. `Empty` is treated
      as a success. The spec returns errors ONLY when no successes exist. This
      constructor allows error results from any derivation tree. The
      success-priority filtering (spec lines 129-134) is captured by
      `EvalAtomFiltered` below, which adds the negative condition as
      a separate Prop (avoiding non-positive occurrence in the inductive). -/
  | interpret_error (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpression space dispatch atom type_ b r)
      (h_is_error : isErrorAtom r.1 = true) :
      EvalAtom space dispatch atom type_ b r

/-- Interpret an expression (dispatch to function or tuple path).
    Ref: spec lines 172-210 "Interpret expression (interpret_expression)".

    Input: expression atom, expected type, bindings.
    Output: one result pair (after metta_call on the interpret result). -/
inductive InterpretExpression (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → Prop where
  /-- Spec lines 190-203: Operator has a valid function type, type check passes.
      ```
      for $f in <function types>:
          match check_if_function_type_is_applicable(...): case Ok($succs):
              for $b in $succs:
                  for ($a, $b) in interpret_function(...):
                      result += metta_call($a, $ret_type, $space, $b)
      ```
      `funcType` is one of the operator's types that is a valid function type.
      `retType` is the return type of `funcType` (or %Undefined% if Expression). -/
  | function_path (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (funcType retType : Atom) (b' : Bindings)
      (interpResult callResult : ResultPair) (fuel : Nat)
      (h_shape : atom = .expression (op :: args))
      (h_op_type : funcType ∈ getAtomTypes space op)
      (h_is_func : isFunctionType funcType = true)
      (succs : List Bindings)
      (h_check : checkIfFunctionTypeIsApplicable atom funcType type_ space b fuel = .inr succs)
      (h_check_b : b' ∈ succs)
      -- retType adjustment: if return type is Expression, use %Undefined%
      (h_ret : retType = (if getFunctionRetType funcType = some Atom.expressionType
                           then Atom.undefinedType
                           else (getFunctionRetType funcType).getD Atom.undefinedType))
      (h_interp : InterpretFunction space dispatch atom funcType type_ b' interpResult)
      (h_call : MettaCall space dispatch interpResult.1 retType interpResult.2 callResult) :
      InterpretExpression space dispatch atom type_ b callResult
  /-- Spec lines 205-209: Tuple fallback path.
      ```
      if <$actual_types contains non function types or %Undefined%>:
          for ($a, $b) in interpret_tuple($atom, $space, $bindings):
              $tuples += metta_call($a, $type, $space, $b)
      ``` -/
  | tuple_path (atom type_ : Atom) (b : Bindings)
      (tupleResult callResult : ResultPair)
      (h_has_non_func : ∃ t ∈ getAtomTypes space (match atom with
                          | .expression (op :: _) => op | _ => atom),
                        isFunctionType t = false ∨ t = Atom.undefinedType)
      (h_tuple : InterpretTuple space dispatch atom b tupleResult)
      (h_call : MettaCall space dispatch tupleResult.1 type_ tupleResult.2 callResult) :
      InterpretExpression space dispatch atom type_ b callResult
  /-- Spec line 184-186: Operator has incorrect type → error.
      ```
      if <$op is an atom with incorrect type>:
          return <list of (Error $op (BadArgType ...))>
      ``` -/
  | op_type_error (atom type_ : Atom) (b : Bindings) (op : Atom) (args : List Atom)
      (errAtom : Atom) (fuel : Nat)
      (h_shape : atom = .expression (op :: args))
      (h_all_fail : ∀ ft ∈ getAtomTypes space op,
        isFunctionType ft = true →
        ∃ errs, checkIfFunctionTypeIsApplicable atom ft type_ space b fuel = .inl errs)
      (h_no_non_func : ∀ t ∈ getAtomTypes space op,
        isFunctionType t = true ∧ t ≠ Atom.undefinedType)
      (h_err : isErrorAtom errAtom = true) :
      InterpretExpression space dispatch atom type_ b (errAtom, b)

/-- Interpret a function call (evaluate head, then args).
    Ref: spec lines 296-321 "Interpret function (interpret_function)".

    Input: expression, function type, return type, bindings.
    Output: one result pair. -/
inductive InterpretFunction (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Atom → Bindings → ResultPair → Prop where
  /-- Spec lines 312-314: Head evaluates to Empty/Error → propagate.
      ```
      for ($h, $hb) in metta($op, $op_type, $space, $bindings):
          if $h == Empty or $h ~ (Error ...):
              $result += [($h, $hb)]
      ``` -/
  | head_error (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (headResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_head : EvalAtom space dispatch op opType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretFunction space dispatch atom opType retType b headResult
  /-- Spec lines 315-320: Head ok, evaluate args, combine.
      ```
      else:
          for ($t, $tb) in interpret_args($args, $arg_types, $space, $hb):
              if $t == Empty or $t ~ (Error ...):
                  $result += [($t, $tb)]
              else:
                  $result += [(<tuple with head $h and tail $t>, $tb)]
      ``` -/
  | head_ok_tail_error (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtom space dispatch op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgs space dispatch args argTypes headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretFunction space dispatch atom opType retType b tailResult
  | head_ok_tail_ok (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtom space dispatch op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgs space dispatch args argTypes headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretFunction space dispatch atom opType retType b
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression es => es | a => [a]), tailResult.2)

/-- Interpret argument list (recursive evaluation of each arg with its type).
    Ref: spec lines 322-347 "Interpret arguments (interpret_args)".

    Input: args list, types list, bindings.
    Output: one result pair (combined args as expression). -/
inductive InterpretArgs (space : Space) (dispatch : GroundedDispatch) :
    List Atom → List Atom → Bindings → ResultPair → Prop where
  /-- Base case: empty args → return unit.
      Implicit in spec (loop terminates when args exhausted). -/
  | nil :
      InterpretArgs space dispatch [] [] b (Atom.unit, b)
  /-- Spec lines 338-340: Head evaluates to Empty/Error AND changed → propagate.
      ```
      for ($h, $hb) in metta($atom, $type, $space, $bindings):
          if ($h == Empty or $h ~ (Error ...)) and $h != $atom:
              $result += [($h, $hb)]
      ``` -/
  | head_changed_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult : ResultPair)
      (h_head : EvalAtom space dispatch a t b headResult)
      (h_err : isEmptyOrError headResult.1 = true)
      (h_changed : headResult.1 ≠ a) :
      InterpretArgs space dispatch (a :: as) (t :: ts) b headResult
  /-- Spec lines 341-346: Head ok (or unchanged error), recurse on tail.
      ```
      else:
          for ($t, $tb) in interpret_args($args_tail, $types_tail, $space, $hb):
              ...
      ``` -/
  | cons_tail_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtom space dispatch a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgs space dispatch as ts headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretArgs space dispatch (a :: as) (t :: ts) b tailResult
  | cons_ok (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtom space dispatch a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgs space dispatch as ts headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretArgs space dispatch (a :: as) (t :: ts) b
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression es => es | x => [x]), tailResult.2)

/-- Interpret a tuple (recursive element-wise evaluation).
    Ref: spec lines 211-233 "Interpret tuple (interpret_tuple)".

    Input: expression atom, bindings.
    Output: one result pair. -/
inductive InterpretTuple (space : Space) (dispatch : GroundedDispatch) :
    Atom → Bindings → ResultPair → Prop where
  /-- Single-element expression: evaluate the element.
      Implicit base case: `(x)` → `metta(x, %Undefined%, space, bindings)`. -/
  | singleton (a : Atom) (b : Bindings) (r : ResultPair)
      (h_eval : EvalAtom space dispatch a Atom.undefinedType b r) :
      InterpretTuple space dispatch (.expression [a]) b r
  /-- Spec lines 224-226: Head evaluates to Empty/Error → propagate.
      ```
      for ($h, $hb) in metta($head, %Undefined%, $space, $bindings):
          if $h == Empty or $h ~ (Error ...):
              $result += [($h, $hb)]
      ``` -/
  | head_error (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtom space dispatch hd Atom.undefinedType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretTuple space dispatch (.expression (hd :: tl)) b headResult
  /-- Spec lines 228-230: Head ok, tail evaluates to Empty/Error → propagate.
      ```
      for ($t, $tb) in interpret_tuple($tail, $space, $hb):
          if $t == Empty or $t ~ (Error ...):
              $result += [($t, $tb)]
      ``` -/
  | tail_error (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtom space dispatch hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTuple space dispatch (.expression tl) headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretTuple space dispatch (.expression (hd :: tl)) b tailResult
  /-- Spec lines 231-232: Both head and tail ok → combine.
      ```
      $result += [(<tuple with head $h and tail $t>, $tb)]
      ``` -/
  | success (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtom space dispatch hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTuple space dispatch (.expression tl) headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretTuple space dispatch (.expression (hd :: tl)) b
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression es => es | a => [a]), tailResult.2)

/-- Call a MeTTa expression (grounded dispatch or equation matching).
    Ref: spec lines 348-389 "Call MeTTa expression (metta_call)".

    Input: atom, expected type, bindings.
    Output: one result pair. -/
inductive MettaCall (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → Prop where
  /-- Spec lines 359-360: Error atoms pass through.
      ```
      if $atom ~ (Error ...):
          return [($atom, $bindings)]
      ``` -/
  | error_passthrough (atom type_ : Atom) (b : Bindings)
      (h_err : isErrorAtom atom = true) :
      MettaCall space dispatch atom type_ b (atom, b)
  /-- Spec lines 365-368: Grounded op, native call succeeds → recurse with metta.
      ```
      if <$op is executable grounded atom>:
          match <call $op native function>: case Ok($results):
              $results = [metta($r, $type, $space, $mb)
                          for ($r, $rb) in $results
                          for $mb in merge_bindings($rb, $bindings)]
      ``` -/
  | grounded_ok (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (nativeResults : ResultSet) (nativeResult : ResultPair)
      (merged : Bindings) (finalResult : ResultPair) (fuel : Nat)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok nativeResults)
      (h_native_mem : nativeResult ∈ nativeResults)
      (h_merge : merged ∈ mergeBindings nativeResult.2 b fuel)
      (h_recurse : EvalAtom space dispatch nativeResult.1 type_ merged finalResult) :
      MettaCall space dispatch atom type_ b finalResult
  /-- Spec lines 369-370: Grounded op, runtime error.
      ```
      case RuntimeError($message):
          return [(Error $atom <message>)]
      ``` -/
  | grounded_runtime_error (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (msg : String)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .runtimeError msg) :
      MettaCall space dispatch atom type_ b
        (Atom.error atom (.symbol msg), b)
  /-- Spec lines 371-372: Grounded op, NoReduce.
      ```
      case NoReduce: return [($atom, $bindings)]
      ``` -/
  | grounded_no_reduce (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .noReduce) :
      MettaCall space dispatch atom type_ b (atom, b)
  /-- Spec lines 371-374: Grounded op, IncorrectArgument.
      ```
      case IncorrectArgument: return [($atom, $bindings)]
      ``` -/
  | grounded_incorrect_arg (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .incorrectArgument) :
      MettaCall space dispatch atom type_ b (atom, b)
  /-- Spec lines 365-368 + 386-387: Grounded op returns empty result list → Empty.
      When `dispatch.execute` returns `.ok []`, the result list is empty, so
      the final `if len($results) == 0` branch applies.
      ```
      case Ok($results):
          ... (but $results is empty)
      if len($results) == 0:
          return [(Empty, $bindings)]
      ``` -/
  | grounded_empty_results (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok []) :
      MettaCall space dispatch atom type_ b (Atom.empty, b)
  /-- Spec lines 376-382: Non-grounded, equation match found → recurse.
      ```
      $query_output = query($space, (= $atom $X))
      if len($query_output) > 0:
          for $rb in $query_output:
              for $mb in merge_bindings($rb, $bindings):
                  if not(<$mb has loop bindings>) and <$mb contains value for $X>:
                      $x = <value of $X from $mb>
                      $results += [metta($x, $type, $space, $mb)]
      ``` -/
  | equation_match (atom type_ : Atom) (b : Bindings)
      (rhs : Atom) (queryBindings merged : Bindings)
      (finalResult : ResultPair) (fuel : Nat)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_query : (rhs, queryBindings) ∈ queryEquations space atom fuel)
      (h_merge : merged ∈ mergeBindings queryBindings b fuel)
      (h_no_loop : merged.hasLoop = false)
      (h_recurse : EvalAtom space dispatch (merged.apply rhs) type_ merged finalResult) :
      MettaCall space dispatch atom type_ b finalResult
  /-- Spec lines 383-384: Non-grounded, no equation matches → return unchanged.
      ```
      else:
          $results += [($atom, $bindings)]
      ``` -/
  | no_match (atom type_ : Atom) (b : Bindings) (fuel : Nat)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_no_eqs : queryEquations space atom fuel = []) :
      MettaCall space dispatch atom type_ b (atom, b)
  /-- Spec lines 386-387: All paths produced no results → return Empty.
      ```
      if len($results) == 0:
          return [(Empty, $bindings)]
      ``` -/
  | empty_results (atom type_ : Atom) (b : Bindings) (fuel : Nat)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_has_eqs : queryEquations space atom fuel ≠ [])
      (h_all_filtered : ∀ (rhs : Atom) (qb mb : Bindings),
        (rhs, qb) ∈ queryEquations space atom fuel →
        mb ∈ mergeBindings qb b fuel →
        mb.hasLoop = true) :
      MettaCall space dispatch atom type_ b (Atom.empty, b)

end

/-! ## Success-Priority Filtering

The spec (lines 129-136) returns successes over errors. Since this requires
a negative condition ("no success derivation exists"), it cannot live inside
the mutual inductive. We define it as a separate Prop. -/

/-- `EvalAtom` with the spec's success-priority filtering.
    A result is "filtered-valid" if either:
    1. It's a success (non-error) result from `interpret_success`, OR
    2. It's an error result AND no success derivation exists for this input.
    For non-interpret constructors (empty_or_error, type_pass, type_cast),
    filtering is vacuous — all results are valid. -/
def EvalAtomFiltered (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  EvalAtom space dispatch atom type_ b r ∧
  (isErrorAtom r.1 = true →
    -- If the result is an error, then no non-error derivation exists.
    -- Note: Empty is NOT an error per spec lines 129-136.
    ∀ r' : ResultPair,
      InterpretExpression space dispatch atom type_ b r' →
      isErrorAtom r'.1 = true)

-- Introduce notation for readability in downstream files
set_option quotPrecheck false in
scoped notation:50 space " ⊢ₘ " atom " : " type_ " | " b " ⇒ " r =>
  EvalAtom space GroundedDispatch.none atom type_ b r

end Mettapedia.Languages.MeTTa.HE
