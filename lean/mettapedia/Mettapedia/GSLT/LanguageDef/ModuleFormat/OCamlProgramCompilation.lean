import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlMachine
import Mettapedia.Languages.OCaml.Scope
import Mettapedia.Languages.OCaml.PatternEquality
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
import Mathlib.Data.Nat.Digits.Defs

/-! Indexed OCaml instructions compile to ordinary root GSLT rules. Runtime
closures contain code references and environments, never grammar trees.
Positive pattern requests use the shared matcher. Failure/next-clause control
and native primitive service installation remain separate runtime joins. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages

def node (label : String) (arguments : List Pattern := []) : Pattern := .apply label arguments
def hole (label : String) : Pattern := .fvar ("ml:" ++ label)
def digits (value : Nat) : Pattern := .collection .vec
  ((Nat.digits 16 value).map fun digit => node ("R16Nibble" ++ toString digit)) none
def code (index : Nat) : Pattern := node "MlCodeNumber" [digits index]
def patternId (index : Nat) : Pattern := node "MlPatternNumber" [digits index]
def tag (typeId constructor : Nat) : Pattern := node "MlTagNumber" [digits typeId, digits constructor]

def linked (cons nil : String) (items : List Pattern) : Pattern :=
  items.foldr (fun head tail => node cons [head, tail]) (node nil)
def values := linked "MlValueCons" "MlValueNil"
def codes := linked "MlCodeCons" "MlCodeNil"
def extend (bindings : List Pattern) (environment : Pattern) : Pattern :=
  bindings.foldl (fun tail head => node "MlEnvironmentCons" [head, tail]) environment

def literal : OCaml.Literal → Pattern
  | .integer value => node "MlInteger"
      [node (if value < 0 then "MlNegative" else "MlNonnegative"), digits value.natAbs]
  | .boolean value => node (if value then "MlTrue" else "MlFalse")
  | .unit => node "MlUnit"
  | .nil => node "MlNil"
  | .string bytes => node "MlString" [.collection .vec (bytes.map fun byte =>
      node "MlByteValue" [node ("R16Nibble" ++ toString (byte.toNat / 16)),
        node ("R16Nibble" ++ toString (byte.toNat % 16))]) none]

def primitive : OCaml.Primitive → Pattern
  | .add => node "MlAdd" | .subtract => node "MlSubtract" | .multiply => node "MlMultiply"
  | .divide => node "MlDivide" | .modulo => node "MlModulo" | .negate => node "MlNegate"
  | .equal => node "MlEqual" | .different => node "MlDifferent" | .less => node "MlLess"
  | .lessEqual => node "MlLessEqual" | .greater => node "MlGreater" | .greaterEqual => node "MlGreaterEqual"
  | .notBool => node "MlNotBool"

mutual
  def value : OCaml.Value → Pattern
    | .literal datum => literal datum
    | .tuple fields => node "MlTuple" [valueList fields]
    | .cons head tail => node "MlCons" [value head, value tail]
    | .variant typeId constructor fields => node "MlVariant" [tag typeId constructor, valueList fields]
    | .closure (.lambda reference) captured => node "MlClosure"
        [node "MlLambdaFunction" [code reference], environment captured]
    | .closure (.recursive group slot) captured => node "MlClosure"
        [node "MlRecursiveFunction" [code group, code slot], environment captured]

  def valueList : List OCaml.Value → Pattern
    | [] => node "MlValueNil"
    | head :: tail => node "MlValueCons" [value head, valueList tail]

  def environment : List OCaml.Value → Pattern
    | [] => node "MlEnvironmentNil"
    | head :: tail => node "MlEnvironmentCons" [value head, environment tail]
end

structure CompiledPattern where
  term : Pattern
  bindings : List Pattern

def fresh : StateM Nat Pattern := do
  let index ← get
  set (index + 1)
  pure (hole ("pattern:" ++ toString index))

mutual
  def compilePattern : OCaml.MatchPattern → StateM Nat CompiledPattern
    | .bind => do let binding ← fresh; pure ⟨binding, [binding]⟩
    | .wildcard => do pure ⟨← fresh, []⟩
    | .literal datum => pure ⟨literal datum, []⟩
    | .tuple fields => do
        let fields ← compilePatternFields fields
        pure ⟨node "MlTuple" [values fields.1], fields.2⟩
    | .cons head tail => do
        let head ← compilePattern head
        let tail ← compilePattern tail
        pure ⟨node "MlCons" [head.term, tail.term], head.bindings ++ tail.bindings⟩
    | .variant typeId constructor fields => do
        let fields ← compilePatternFields fields
        pure ⟨node "MlVariant" [tag typeId constructor, values fields.1], fields.2⟩

  def compilePatternFields : List OCaml.MatchPattern → StateM Nat (List Pattern × List Pattern)
    | [] => pure ([], [])
    | first :: rest => do
        let first ← compilePattern first
        let rest ← compilePatternFields rest
        pure (first.term :: rest.1, first.bindings ++ rest.2)
end

def patterns (program : OCaml.Program) : List OCaml.MatchPattern :=
  program.code.toList.flatMap fun instruction => match instruction with
    | .lambda pattern _ | .letValue pattern _ _ => [pattern]
    | .matchValue _ clauses => clauses.map (·.pattern)
    | _ => []

def patternReference? (pool : List OCaml.MatchPattern) (pattern : OCaml.MatchPattern) : Option Pattern :=
  OCaml.patternIndex? pattern pool |>.map patternId

def rule (name : String) (left right : Pattern) : RewriteRule :=
  { name := name, typeContext := [], left := left, right := right, premises := [] }

def recursiveEnvironment (group : Nat) (definitions : List OCaml.Code) (environment : Pattern) : Pattern :=
  extend ((List.range definitions.length).map fun slot => node "MlClosure"
    [node "MlRecursiveFunction" [code group, code slot], environment]) environment

def startArguments (kind : Pattern) (arguments : List OCaml.Code) (environment continuation : Pattern) : Pattern :=
  match arguments.reverse with
  | [] => node "MlBuildConfig" [kind, values [], continuation]
  | last :: rest => node "MlEvaluate" [code last, environment,
      node "MlKBuild" [kind, codes (rest.map code), environment, values [], continuation]]

def clauseList? (pool : List OCaml.MatchPattern) (clauses : List OCaml.Clause) : Option Pattern := do
  let entries ← clauses.mapM fun clause => do
    pure (← patternReference? pool clause.pattern, code clause.body)
  pure (entries.foldr (fun (pattern, body) rest => node "MlClauseCons" [pattern, body, rest]) (node "MlClauseNil"))

def compileInstruction? (pool : List OCaml.MatchPattern) (reference : Nat)
    (instruction : OCaml.Instruction) : Option RewriteRule := do
  let environment := hole "environment"
  let continuation := hole "continuation"
  let left := node "MlEvaluate" [code reference, environment, continuation]
  let returned := fun datum => node "MlReturn" [datum, continuation]
  let evaluate := fun target env rest => node "MlEvaluate" [code target, env, rest]
  let next ← match instruction with
    | .literal datum => pure (left, returned (literal datum))
    | .variable index =>
        let tail := hole "tail"
        let wanted := hole "variable"
        let skipped := (List.range index).map fun skip => hole ("skip:" ++ toString skip)
        let input := extend skipped.reverse (node "MlEnvironmentCons" [wanted, tail])
        pure (node "MlEvaluate" [code reference, input, continuation], returned wanted)
    | .lambda _ _ => pure (left, returned (node "MlClosure" [node "MlLambdaFunction" [code reference], environment]))
    | .apply function argument => pure (left, evaluate argument environment
        (node "MlKArgument" [code function, environment, continuation]))
    | .letValue pattern argument body => do
        pure (left, evaluate argument environment (node "MlKLet"
          [← patternReference? pool pattern, code body, environment, continuation]))
    | .letRecursive definitions body =>
        pure (left, evaluate body (recursiveEnvironment reference definitions environment) continuation)
    | .branch condition yes no => pure (left, evaluate condition environment
        (node "MlKBranch" [code yes, code no, environment, continuation]))
    | .andThen first second => pure (left, evaluate first environment
        (node "MlKAnd" [code second, environment, continuation]))
    | .orElse first second => pure (left, evaluate first environment
        (node "MlKOr" [code second, environment, continuation]))
    | .tuple fields => pure (left, startArguments (node "MlBuildTuple") fields environment continuation)
    | .variant typeId constructor fields =>
        pure (left, startArguments (node "MlBuildVariant" [tag typeId constructor]) fields environment continuation)
    | .primitive operator arguments => pure (left,
        startArguments (node "MlBuildPrimitive" [primitive operator]) arguments environment continuation)
    | .cons head tail => pure (left, evaluate tail environment (node "MlKConsTail" [code head, environment, continuation]))
    | .matchValue scrutinee clauses => do
        pure (left, evaluate scrutinee environment (node "MlKMatch" [← clauseList? pool clauses, environment, continuation]))
  pure (rule ("ml-code:" ++ toString reference) next.1 next.2)

def patternRules (index : Nat) (pattern : OCaml.MatchPattern) : List RewriteRule :=
  let compiled := ((compilePattern pattern).run 0).1
  let environment := hole "environment"
  let body := hole "body"
  let continuation := hole "continuation"
  let right := node "MlEvaluate" [body, extend compiled.bindings environment, continuation]
  [rule ("ml-pattern-one:" ++ toString index)
    (node "MlMatchOne" [patternId index, compiled.term, body, environment, continuation]) right,
   rule ("ml-pattern-clause:" ++ toString index)
    (node "MlTryClause" [patternId index, compiled.term, body, hole "later", environment, continuation]) right]

def functionRules? (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference : Nat) (instruction : OCaml.Instruction) : Option (List RewriteRule) := do
  let environment := hole "environment"
  let argument := hole "argument"
  let continuation := hole "continuation"
  match instruction with
  | .lambda pattern body =>
      pure [rule ("ml-function:" ++ toString reference)
        (node "MlApply" [node "MlClosure" [node "MlLambdaFunction" [code reference], environment], argument, continuation])
        (node "MlMatchOne" [← patternReference? pool pattern, argument, code body, environment, continuation])]
  | .letRecursive definitions _ => definitions.zipIdx.mapM fun (referenceToFunction, slot) => do
      let some (.lambda pattern body) := program.instruction? referenceToFunction | none
      pure (rule ("ml-recursive:" ++ toString reference ++ ":" ++ toString slot)
        (node "MlApply" [node "MlClosure" [node "MlRecursiveFunction" [code reference, code slot], environment], argument, continuation])
        (node "MlMatchOne" [← patternReference? pool pattern, argument, code body,
          recursiveEnvironment reference definitions environment, continuation]))
  | _ => pure []

structure Prepared where
  program : OCaml.Program
  patternPool : List OCaml.MatchPattern
  compiled : LanguageDef
  deriving Repr

def prepare (program : OCaml.Program) : Except String Prepared := do
  unless program.checkScope do throw "OCaml indexed code has invalid scope or unsupported data formation"
  let pool := patterns program
  let dispatch ← program.code.toList.zipIdx.mapM fun (instruction, reference) => do
    let some compiled := compileInstruction? pool reference instruction | throw "instruction compilation refused"
    pure compiled
  let functions ← program.code.toList.zipIdx.mapM fun (instruction, reference) => do
    let some compiled := functionRules? program pool reference instruction | throw "function compilation refused"
    pure compiled
  let patternRules := pool.zipIdx.flatMap fun (pattern, index) => patternRules index pattern
  let language : LanguageDef := { baseLanguage with
    name := "OCamlIndexedMachine"
    rewrites := baseLanguage.rewrites ++ dispatch ++ functions.flatten ++ patternRules }
  unless language.validate.isEmpty do throw s!"invalid compiled declarations: {reprStr language.validate}"
  pure ⟨program, pool, language⟩

def provider : GeneralPremise.ProviderSnapshot where
  signatures := [⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"],
    [.input, .input, .output]⟩,
    ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩]
  rows := []

def snapshot (prepared : Prepared) : GeneralExecutionAdmission.Snapshot := ⟨prepared.compiled, [], provider⟩
def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly, includeDerivedEquations := false}
def plan (prepared : Prepared) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot prepared) permissions

def initial (program : OCaml.Program) : Pattern :=
  node "MlEvaluate" [code program.entry, node "MlEnvironmentNil", node "MlKDone"]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
