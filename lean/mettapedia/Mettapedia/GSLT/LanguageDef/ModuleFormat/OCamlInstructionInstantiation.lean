import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateEncoding
import Mettapedia.OSLF.MeTTaIL.Match

/-! Actual indexed instruction-rule bodies under their runtime bindings.
Code and literal data remain fixed; captured environments and complete
continuations are substituted through the same rule representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def instructionBindings (captured continuation : Pattern) : Bindings :=
  [("ml:environment", captured), ("ml:continuation", continuation)]

theorem apply_node (bindings : Bindings) (label : String) (arguments : List Pattern) :
    applyBindings bindings (node label arguments) = node label (arguments.map (applyBindings bindings)) := by
  rw [node, applyBindings]
  rfl

theorem apply_digits (bindings : Bindings) (index : Nat) : applyBindings bindings (digits index) = digits index := by
  simp only [digits, applyBindings, List.append_nil]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro digit _
  simp only [Function.comp_apply, node, applyBindings, List.map_nil]

theorem apply_code (bindings : Bindings) (index : Nat) : applyBindings bindings (code index) = code index := by
  simp only [code, apply_node, List.map_cons, List.map_nil, apply_digits]

theorem apply_tag (bindings : Bindings) (typeId constructor : Nat) :
    applyBindings bindings (tag typeId constructor) = tag typeId constructor := by
  simp only [tag, apply_node, List.map_cons, List.map_nil, apply_digits]

theorem apply_linked (bindings : Bindings) (cons nil : String) (items : List Pattern) :
    applyBindings bindings (linked cons nil items) = linked cons nil (items.map (applyBindings bindings)) := by
  induction items with
  | nil => simp only [linked, List.foldr_nil, apply_node, List.map_nil]
  | cons first rest ih =>
    simpa only [linked, List.foldr_cons, apply_node, List.map_cons, List.map_nil] using
      congrArg (fun tail => node cons [applyBindings bindings first, tail]) ih

theorem apply_literal (bindings : Bindings) (datum : OCaml.Literal) :
    applyBindings bindings (literal datum) = literal datum := by
  cases datum with
  | integer number => simp only [literal, apply_node, List.map_cons, List.map_nil, apply_digits]
  | boolean value => simp only [literal, apply_node, List.map_nil]
  | unit => simp only [literal, apply_node, List.map_nil]
  | nil => simp only [literal, apply_node, List.map_nil]
  | string bytes =>
    simp only [literal, apply_node, List.map_cons, List.map_nil, applyBindings, List.append_nil]
    congr 2
    rw [List.map_map]
    apply congrArg (fun items => Pattern.collection .vec items none)
    apply List.map_congr_left
    intro byte _
    simp only [Function.comp_apply, apply_node, List.map_cons, List.map_nil]

theorem apply_primitive (bindings : Bindings) (operator : OCaml.Primitive) :
    applyBindings bindings (primitive operator) = primitive operator := by
  cases operator <;> simp only [primitive, apply_node, List.map_nil]

theorem apply_environment_hole (captured continuation : Pattern) :
    applyBindings (instructionBindings captured continuation) (hole "environment") = captured := by
  simp [instructionBindings, hole, applyBindings]

theorem apply_continuation_hole (captured continuation : Pattern) :
    applyBindings (instructionBindings captured continuation) (hole "continuation") = continuation := by
  simp [instructionBindings, hole, applyBindings]

theorem apply_extend (bindings : Bindings) (values : List Pattern) (captured : Pattern) :
    applyBindings bindings (extend values captured) =
      extend (values.map (applyBindings bindings)) (applyBindings bindings captured) := by
  induction values generalizing captured with
  | nil => rfl
  | cons first rest ih =>
    simp only [extend, List.foldl_cons, List.map_cons] at *
    rw [ih]
    simp only [apply_node, List.map_cons, List.map_nil]

theorem apply_recursiveEnvironment (bindings : Bindings) (group : Nat) (definitions : List OCaml.Code)
    (captured : Pattern) :
    applyBindings bindings (recursiveEnvironment group definitions captured) =
      recursiveEnvironment group definitions (applyBindings bindings captured) := by
  simp only [recursiveEnvironment, apply_extend, List.map_map, Function.comp_def,
    apply_node, List.map_cons, List.map_nil, apply_code]

def instructionResult? (pool : List OCaml.MatchPattern) (reference : Nat) (instruction : OCaml.Instruction)
    (captured continuation : Pattern) : Option Pattern := do
  let compiled ← compileInstruction? pool reference instruction
  pure (applyBindings (instructionBindings captured continuation) compiled.right)

theorem literal_instruction (pool : List OCaml.MatchPattern) (reference : Nat) (datum : OCaml.Literal)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.literal datum) captured continuation =
      some (node "MlReturn" [literal datum, continuation]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_literal, apply_continuation_hole]

theorem lambda_instruction (pool : List OCaml.MatchPattern) (reference body : Nat) (pattern : OCaml.MatchPattern)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.lambda pattern body) captured continuation =
      some (node "MlReturn" [node "MlClosure" [node "MlLambdaFunction" [code reference], captured], continuation]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_environment_hole, apply_continuation_hole]

theorem application_instruction (pool : List OCaml.MatchPattern) (reference function argument : Nat)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.apply function argument) captured continuation =
      some (node "MlEvaluate" [code argument, captured, node "MlKArgument" [code function, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_environment_hole, apply_continuation_hole]

theorem recursive_instruction (pool : List OCaml.MatchPattern) (reference body : Nat) (definitions : List OCaml.Code)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.letRecursive definitions body) captured continuation =
      some (node "MlEvaluate" [code body, recursiveEnvironment reference definitions captured, continuation]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_recursiveEnvironment, apply_environment_hole, apply_continuation_hole]

theorem branch_instruction (pool : List OCaml.MatchPattern) (reference condition yes no : Nat)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.branch condition yes no) captured continuation =
      some (node "MlEvaluate" [code condition, captured, node "MlKBranch" [code yes, code no, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_environment_hole, apply_continuation_hole]

theorem and_instruction (pool : List OCaml.MatchPattern) (reference left right : Nat)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.andThen left right) captured continuation =
      some (node "MlEvaluate" [code left, captured, node "MlKAnd" [code right, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_environment_hole, apply_continuation_hole]

theorem or_instruction (pool : List OCaml.MatchPattern) (reference left right : Nat)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.orElse left right) captured continuation =
      some (node "MlEvaluate" [code left, captured, node "MlKOr" [code right, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_environment_hole, apply_continuation_hole]

theorem cons_instruction (pool : List OCaml.MatchPattern) (reference head tail : Nat)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.cons head tail) captured continuation =
      some (node "MlEvaluate" [code tail, captured, node "MlKConsTail" [code head, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, apply_node, List.map_cons, List.map_nil,
    apply_code, apply_environment_hole, apply_continuation_hole]

theorem patternReference?_fixed (bindings : Bindings) {pool : List OCaml.MatchPattern} {pattern : OCaml.MatchPattern}
    {reference : Pattern} (found : patternReference? pool pattern = some reference) :
    applyBindings bindings reference = reference := by
  unfold patternReference? at found
  obtain ⟨index, _, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  simp only [patternId, apply_node, List.map_cons, List.map_nil, apply_digits]

theorem let_instruction {pool : List OCaml.MatchPattern} (reference argument body : Nat)
    {pattern : OCaml.MatchPattern} {patternCode : Pattern} (found : patternReference? pool pattern = some patternCode)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.letValue pattern argument body) captured continuation =
      some (node "MlEvaluate" [code argument, captured,
        node "MlKLet" [patternCode, code body, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule, found, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [apply_node, List.map_cons, List.map_nil, apply_code,
    patternReference?_fixed _ found, apply_environment_hole, apply_continuation_hole]

theorem apply_codes (bindings : Bindings) (references : List OCaml.Code) :
    applyBindings bindings (codes (references.map code)) = codes (references.map code) := by
  simp only [codes, apply_linked, List.map_map, Function.comp_def, apply_code]

theorem apply_startArguments (bindings : Bindings) (kind : Pattern) (arguments : List OCaml.Code)
    (captured continuation : Pattern) :
    applyBindings bindings (startArguments kind arguments captured continuation) =
      startArguments (applyBindings bindings kind) arguments (applyBindings bindings captured)
        (applyBindings bindings continuation) := by
  unfold startArguments
  cases arguments.reverse with
  | nil => simp only [apply_node, List.map_cons, List.map_nil, values, apply_linked]
  | cons last rest => simp only [apply_node, List.map_cons, List.map_nil, apply_code, apply_codes,
      values, apply_linked]

theorem tuple_instruction (pool : List OCaml.MatchPattern) (reference : Nat) (fields : List OCaml.Code)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.tuple fields) captured continuation =
      some (startArguments (node "MlBuildTuple") fields captured continuation) := by
  simp only [instructionResult?, compileInstruction?, rule, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [apply_startArguments, apply_node, List.map_nil, apply_environment_hole, apply_continuation_hole]

theorem variant_instruction (pool : List OCaml.MatchPattern) (reference typeId constructor : Nat)
    (fields : List OCaml.Code) (captured continuation : Pattern) :
    instructionResult? pool reference (.variant typeId constructor fields) captured continuation =
      some (startArguments (node "MlBuildVariant" [tag typeId constructor]) fields captured continuation) := by
  simp only [instructionResult?, compileInstruction?, rule, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [apply_startArguments, apply_node, List.map_cons, List.map_nil, apply_tag,
    apply_environment_hole, apply_continuation_hole]

theorem primitive_instruction (pool : List OCaml.MatchPattern) (reference : Nat) (operator : OCaml.Primitive)
    (arguments : List OCaml.Code) (captured continuation : Pattern) :
    instructionResult? pool reference (.primitive operator arguments) captured continuation =
      some (startArguments (node "MlBuildPrimitive" [primitive operator]) arguments captured continuation) := by
  simp only [instructionResult?, compileInstruction?, rule, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [apply_startArguments, apply_node, List.map_cons, List.map_nil, apply_primitive,
    apply_environment_hole, apply_continuation_hole]

theorem clauseList?_nil (pool : List OCaml.MatchPattern) :
    clauseList? pool [] = some (node "MlClauseNil") := rfl

theorem clauseList?_cons (pool : List OCaml.MatchPattern) (clause : OCaml.Clause) (rest : List OCaml.Clause) :
    clauseList? pool (clause :: rest) = (do
      let reference ← patternReference? pool clause.pattern
      let later ← clauseList? pool rest
      pure (node "MlClauseCons" [reference, code clause.body, later])) := by
  simp only [clauseList?, List.mapM_cons, Option.bind_eq_bind]
  cases patternReference? pool clause.pattern <;>
    cases rest.mapM (fun clause => do pure (← patternReference? pool clause.pattern, code clause.body)) <;> rfl

theorem clauseList?_fixed (bindings : Bindings) {pool : List OCaml.MatchPattern} {clauses : List OCaml.Clause}
    {encoded : Pattern} (found : clauseList? pool clauses = some encoded) :
    applyBindings bindings encoded = encoded := by
  induction clauses generalizing encoded with
  | nil =>
    rw [clauseList?_nil] at found
    cases Option.some.inj found
    simp only [apply_node, List.map_nil]
  | cons first rest ih =>
    rw [clauseList?_cons] at found
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨reference, referenced, later, remaining, rfl⟩ := found
    simp only [apply_node, List.map_cons, List.map_nil,
      patternReference?_fixed bindings referenced, apply_code, ih remaining]

theorem match_instruction {pool : List OCaml.MatchPattern} (reference scrutinee : Nat)
    {clauses : List OCaml.Clause} {encoded : Pattern} (found : clauseList? pool clauses = some encoded)
    (captured continuation : Pattern) :
    instructionResult? pool reference (.matchValue scrutinee clauses) captured continuation =
      some (node "MlEvaluate" [code scrutinee, captured, node "MlKMatch" [encoded, captured, continuation]]) := by
  simp only [instructionResult?, compileInstruction?, rule, found, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [apply_node, List.map_cons, List.map_nil, apply_code,
    clauseList?_fixed _ found, apply_environment_hole, apply_continuation_hole]

theorem variable_instruction (pool : List OCaml.MatchPattern) (reference index : Nat)
    (wanted continuation : Pattern) (rest : Bindings)
    {compiled : RewriteRule} (formed : compileInstruction? pool reference (.variable index) = some compiled) :
    applyBindings (("ml:variable", wanted) :: ("ml:continuation", continuation) :: rest) compiled.right =
      node "MlReturn" [wanted, continuation] := by
  simp only [compileInstruction?, rule, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at formed
  cases formed
  simp [apply_node, hole, applyBindings]

#print axioms application_instruction
#print axioms recursive_instruction

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
