import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSequentialMachine
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
import Mettapedia.Languages.Erlang.Scope
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Static instruction and clause compilation for the indexed Erlang arena.
Code references, definition slots and clause origins remain explicit. Pattern
success uses the existing shared matcher; exhausted matching and primitive
answers have separate declared service ports. No program results or execution
traces are computed during preparation. Source/target adequacy and the native
service controller remain separate qualification obligations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages

def node (label : String) (arguments : List Pattern := []) : Pattern := .apply label arguments
def hole (name : String) : Pattern := .fvar ("er:" ++ name)
def word (value : Nat) : Pattern := .collection .vec
  ((Nat.digits 16 value).map fun digit => node ("R16Nibble" ++ toString digit)) none
def code (reference : Nat) : Pattern := node "ErCodeNumber" [word reference]
def count : Nat → Pattern
  | 0 => node "ErZero"
  | value + 1 => node "ErSucc" [count value]
def patternId (reference slot : Nat) : Pattern := node "ErPatternAt" [code reference, count slot]
def linked (cons nil : String) (items : List Pattern) : Pattern :=
  items.foldr (fun head tail => node cons [head, tail]) (node nil)
def values := linked "ErValuesCons" "ErValuesNil"
def codes := linked "ErCodesCons" "ErCodesNil"
def extend (bindings : List Pattern) (environment : Pattern) : Pattern :=
  bindings.foldl (fun tail head => node "ErEnvironmentCons" [head, tail]) environment

def literal : Erlang.Literal → Pattern
  | .atom name => ErlangMailbox.atom name
  | .integer value => ErlangMailbox.integer value
  | .nil => node "ErNil"

mutual
  def value : Erlang.Value → Pattern
    | .literal datum => literal datum
    | .pid identity => node "ErPid" [word identity]
    | .tuple fields => node "ErTuple" [valueList fields]
    | .cons head tail => node "ErCons" [value head, value tail]
    | .closure arity function captured => node "ErClosure" [count arity,
        (match function with
          | .lambda reference => node "ErLambdaFunction" [code reference]
          | .recursive group slot => node "ErRecursiveFunction" [code group, count slot]), environment captured]

  def valueList : List Erlang.Value → Pattern
    | [] => node "ErValuesNil"
    | head :: tail => node "ErValuesCons" [value head, valueList tail]

  def environment : List Erlang.Value → Pattern
    | [] => node "ErEnvironmentNil"
    | head :: tail => node "ErEnvironmentCons" [value head, environment tail]
end

def fault : Erlang.Fault → Pattern
  | .badarith => node "ErBadarith"
  | .badarg => node "ErBadarg"
  | .badfun actual => node "ErBadfun" [value actual]
  | .badarity function arguments => node "ErBadarity" [value function, valueList arguments]
  | .caseClause arguments => node "ErCaseClause" [valueList arguments]
  | .matchFail reason => node "ErMatchFail" [value reason]

def primitive : Erlang.Primitive → Pattern
  | .add => node "ErAdd" | .subtract => node "ErSubtract" | .multiply => node "ErMultiply"
  | .divide => node "ErDivide" | .remainder => node "ErRemainder" | .negate => node "ErNegate"
  | .equal => node "ErEqual" | .different => node "ErDifferent" | .less => node "ErLess"
  | .lessEqual => node "ErLessEqual" | .greater => node "ErGreater" | .greaterEqual => node "ErGreaterEqual"
  | .isInteger => node "ErIsInteger" | .isAtom => node "ErIsAtom" | .isTuple => node "ErIsTuple"
  | .isList => node "ErIsList" | .isPid => node "ErIsPid" | .isFunction => node "ErIsFunction"
  | .isFunctionArity => node "ErIsFunctionArity" | .andBool => node "ErAnd" | .orBool => node "ErOr"
  | .xorBool => node "ErXor" | .notBool => node "ErNot"

def actor : Erlang.ActorOperation → Pattern
  | .self => node "ErSelf" | .spawn => node "ErSpawn" | .send => node "ErSend"
  | .peekMessage => node "ErPeekMessage" | .nextMessage => node "ErNextMessage"
  | .removeMessage => node "ErRemoveMessage" | .waitInfinity => node "ErWaitInfinity"

def recursiveEnvironment (group : Nat) (definitions : List Erlang.FunctionDefinition) (captured : Pattern) : Pattern :=
  extend (definitions.zipIdx.map fun (definition, slot) => node "ErClosure"
    [count definition.arity, node "ErRecursiveFunction" [code group, count slot], captured]) captured

def clauses (reference : Nat) (clauses : List Erlang.Clause) : Pattern :=
  clauses.zipIdx.foldr (fun (clause, slot) rest => node "ErClausesCons"
    [patternId reference slot, code clause.guard, code clause.body, rest]) (node "ErClausesNil")

def rule (name : String) (left right : Pattern) : RewriteRule :=
  {name := name, typeContext := [], left := left, right := right, premises := []}

def compileInstruction (reference : Nat) (instruction : Erlang.Instruction) : RewriteRule :=
  let env := hole "environment"
  let rest := hole "continuation"
  let left := node "ErEvaluate" [code reference, env, rest]
  let evaluate := fun target scope continuation => node "ErEvaluate" [code target, scope, continuation]
  let start := fun kind arguments => node "ErStart" [kind, codes (arguments.map code), env, rest]
  let right := match instruction with
    | .literal datum => node "ErReturn" [values [literal datum], rest]
    | .variable index => node "ErLookup" [count index, env, count index, env, rest]
    | .lambda arity _ => node "ErReturn"
        [values [node "ErClosure" [count arity, node "ErLambdaFunction" [code reference], env]], rest]
    | .apply function arguments => evaluate function env
        (node "ErKApply" [codes (arguments.map code), env, rest])
    | .letValues arity argument body => evaluate argument env
        (node "ErKLet" [count arity, code body, env, rest])
    | .letRecursive definitions body => evaluate body (recursiveEnvironment reference definitions env) rest
    | .sequence first second => evaluate first env (node "ErKSequence" [code second, env, rest])
    | .values fields => start (node "ErBuildValues") fields
    | .tuple fields => start (node "ErBuildTuple") fields
    | .cons head tail => start (node "ErBuildCons") [head, tail]
    | .caseValues argument alternatives => evaluate argument env
        (node "ErKCase" [clauses reference alternatives, env, rest])
    | .primitive operator arguments => start (node "ErBuildPrimitive" [primitive operator]) arguments
    | .actor operation arguments => start (node "ErBuildActor" [actor operation]) arguments
    | .matchFail reason => evaluate reason env (node "ErKMatchFail" [rest])
  rule ("er-code:" ++ toString reference) left right

def functionRules (reference : Nat) (instruction : Erlang.Instruction) : List RewriteRule :=
  let captured := hole "captured"
  let arguments := hole "arguments"
  let rest := hole "continuation"
  let make := fun (name : String) (arity : Nat) (function scope : Pattern) (body : Nat) =>
    let closure := node "ErClosure" [count arity, function, captured]
    rule name (node "ErApply" [closure, arguments, rest])
      (node "ErBindCall" [count arity, arguments, scope, code body, closure, arguments, rest])
  match instruction with
  | .lambda arity body =>
      [make ("er-function:" ++ toString reference) arity (node "ErLambdaFunction" [code reference]) captured body]
  | .letRecursive definitions _ => definitions.zipIdx.map fun (definition, slot) =>
      make ("er-recursive:" ++ toString reference ++ ":" ++ toString slot) definition.arity
        (node "ErRecursiveFunction" [code reference, count slot])
        (recursiveEnvironment reference definitions captured) definition.body
  | _ => []

structure CompiledPattern where
  term : Pattern
  bindings : List Pattern

def fresh : StateM Nat Pattern := do
  let index ← get
  set (index + 1)
  pure (hole ("match:" ++ toString index))

mutual
  def compilePattern : Erlang.MatchPattern → StateM Nat CompiledPattern
    | .bind => do let capture ← fresh; pure ⟨capture, [capture]⟩
    | .wildcard => do pure ⟨← fresh, []⟩
    | .literal datum => pure ⟨literal datum, []⟩
    | .pinned index => pure ⟨hole ("pin:" ++ toString index), []⟩
    | .alias pattern => do
        let compiled ← compilePattern pattern
        pure ⟨compiled.term, compiled.term :: compiled.bindings⟩
    | .tuple fields => do
        let compiled ← compilePatterns fields
        pure ⟨node "ErTuple" [values compiled.1], compiled.2⟩
    | .cons head tail => do
        let head ← compilePattern head
        let tail ← compilePattern tail
        pure ⟨node "ErCons" [head.term, tail.term], head.bindings ++ tail.bindings⟩

  def compilePatterns : List Erlang.MatchPattern → StateM Nat (List Pattern × List Pattern)
    | [] => pure ([], [])
    | head :: tail => do
        let head ← compilePattern head
        let tail ← compilePatterns tail
        pure (head.term :: tail.1, head.bindings ++ tail.2)
end

mutual
  def pinnedSlots : Erlang.MatchPattern → List Nat
    | .pinned index => [index]
    | .alias pattern => pinnedSlots pattern
    | .tuple fields => pinnedFields fields
    | .cons head tail => pinnedSlots head ++ pinnedSlots tail
    | _ => []
  def pinnedFields : List Erlang.MatchPattern → List Nat
    | [] => []
    | head :: tail => pinnedSlots head ++ pinnedFields tail
end

def environmentPattern (patterns : List Erlang.MatchPattern) : Pattern :=
  let slots := pinnedFields patterns
  if slots.isEmpty then hole "environment"
  else (List.range (slots.foldl Nat.max 0 + 1)).foldr (fun index tail =>
      node "ErEnvironmentCons" [hole ("pin:" ++ toString index), tail]) (hole "environment-tail")

def patternRule (reference slot : Nat) (clause : Erlang.Clause) : RewriteRule :=
  let compiled := ((compilePatterns clause.patterns).run 0).1
  let arguments := values compiled.1
  let outer := environmentPattern clause.patterns
  let bound := extend compiled.2 outer
  let later := hole "later"
  let rest := hole "continuation"
  rule ("er-pattern:" ++ toString reference ++ ":" ++ toString slot)
    (node "ErTryClause" [patternId reference slot, arguments, outer, code clause.guard, code clause.body, later, rest])
    (node "ErEvaluate" [code clause.guard, bound,
      node "ErKGuard" [arguments, later, code clause.body, bound, outer, rest]])

def patterns (reference : Nat) (instruction : Erlang.Instruction) : List RewriteRule := match instruction with
  | .caseValues _ alternatives => alternatives.zipIdx.map fun (clause, slot) => patternRule reference slot clause
  | _ => []

def nonFunctionRules : List RewriteRule :=
  [("ErAtom", 1), ("ErInteger", 2), ("ErPid", 1), ("ErNil", 0), ("ErCons", 2), ("ErTuple", 1)].map fun (label, arity) =>
    let actual := node label ((List.range arity).map fun index => hole ("nonfunction:" ++ toString index))
    rule ("er-nonfunction:" ++ label) (node "ErApply" [actual, hole "arguments", hole "continuation"])
      (node "ErRaise" [node "ErBadfun" [actual], hole "continuation"])

structure Prepared where
  program : Erlang.Program
  initialDepth : Nat
  compiled : LanguageDef
  deriving Repr

def prepare (program : Erlang.Program) (initialDepth : Nat := 0) : Except String Prepared := do
  unless program.checkScope initialDepth do throw "Erlang indexed code has invalid scope, guard effects or opcode arity"
  let dispatch := program.code.toList.zipIdx.map fun (instruction, reference) => compileInstruction reference instruction
  let functions := program.code.toList.zipIdx.flatMap fun (instruction, reference) => functionRules reference instruction
  let matchingRules := program.code.toList.zipIdx.flatMap fun (instruction, reference) => patterns reference instruction
  let language : LanguageDef := {baseLanguage with
    name := "ErlangIndexedMachine"
    rewrites := baseLanguage.rewrites ++ dispatch ++ functions ++ matchingRules ++ nonFunctionRules}
  unless language.validate.isEmpty do throw s!"invalid compiled Erlang declarations: {reprStr language.validate}"
  pure ⟨program, initialDepth, language⟩

def provider : GeneralPremise.ProviderSnapshot where
  signatures := [
    ⟨"er-primitive", [.base "ErPrimitive", .base "ErValues", .base "ErPrimitiveResult"], [.input, .input, .output]⟩,
    ⟨"er-pattern-failure", [.base "ErPatternId", .base "ErValues", .base "ErEnvironment"], [.input, .input, .input]⟩,
    ⟨"er-guard", [.base "ErValues", .base "ErDecision"], [.input, .output]⟩]
  rows := []

def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly, includeDerivedEquations := false}
def plan (prepared : Prepared) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨prepared.compiled, [], provider⟩ permissions

def initial (program : Erlang.Program) (captured : List Erlang.Value := []) : Pattern :=
  node "ErEvaluate" [code program.entry, environment captured, node "ErKDone"]

end ErlangCompilation
