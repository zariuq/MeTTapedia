import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Authored rules for the existing PeTTa configuration representation

The left and right sides expose the control constructors, continuation frames
and I/O fields of the existing configuration codec. Computational premises
name substitution, argument demand, ordered matching and primitive operations;
no premise asks for an evaluator step or a whole-program derivation.

The carrier and operational judgment remain those of the consolidated PeTTa
modules. The authored frontier is exactly the existing transition relation on
represented configurations. Finite store support is carried through actual
steps, and generated paths preserve and reflect completed store and ordered
answer/input/output observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.TypeSynthesis
open ConfigurationEncoding

private def v (name : String) : Pattern := .fvar name

/-- Ordered expression fields in the shared Atom codec. -/
def expressionPattern (fields : List Pattern) (rest : Option String := none) : Pattern :=
  .apply "ground-atom-expression-v1" [.collection .vec fields rest]

def symbolPattern (name : String) : Pattern := OSLFCore.Bridge.GroundData.encode (.symbol name)

def stringPattern (name : String) : Pattern :=
  OSLFCore.Bridge.GroundData.encode (.grounded (.string name))

private theorem symbolPattern_explicit (name : String) : symbolPattern name =
    .apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] := by
  simp only [symbolPattern, OSLFCore.Bridge.GroundData.encode]
  rfl

private theorem stringPattern_explicit (name : String) : stringPattern name =
    .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] := by
  simp only [stringPattern, OSLFCore.Bridge.GroundData.encode]
  rfl

def taggedPattern (tag : String) (fields : List Pattern) : Pattern :=
  expressionPattern (symbolPattern tag :: fields)

def configurationPattern (state control frames input output : Pattern) : Pattern :=
  taggedPattern "petta-configuration-v1" [state, control, frames, input, output]

def evaluatePattern (bindings expression : Pattern) : Pattern :=
  taggedPattern "petta-control-evaluate-v1" [bindings, expression]

def argumentsPattern (bindings target remaining values position : Pattern) : Pattern :=
  taggedPattern "petta-control-arguments-v1" [bindings, target, remaining, values, position]

def sequencePattern (pending answers : Pattern) : Pattern :=
  taggedPattern "petta-control-sequence-v1" [pending, answers]

def returnedPattern (answers : Pattern) : Pattern :=
  taggedPattern "petta-control-returned-v1" [answers]

def faultPattern (reason : Pattern) : Pattern :=
  taggedPattern "petta-control-fault-v1" [reason]

def functionPattern (head : Pattern) : Pattern :=
  taggedPattern "petta-target-function-v1" [head]

def framePattern (tag : String) (fields : List Pattern) : Pattern := taggedPattern tag fields

private def query (name : String) (arguments : List Pattern) : Premise :=
  .relationQuery name arguments

private def atomNames : List String :=
  ["state", "bindings", "target", "remaining", "values", "position", "answers", "first",
    "pending", "frames", "input", "output", "code", "pattern", "body", "rows", "cases",
    "condition", "yes", "no", "expression", "head", "after", "reason", "nested",
    "substituted", "alternatives", "collected", "combined", "successors", "name", "value"]

private def vectorNames : List String := ["pendingTail", "framesTail", "inputTail", "rowsTail", "alternativesTail"]

private def literalNames : List String := ["spelling"]

private def ruleContext : List (String × TypeExpr) :=
  (atomNames.map (fun name => (name, .base "GroundAtom"))) ++
    (vectorNames.map (fun name => (name, .collection .vec (.base "GroundAtom")))) ++
    (literalNames.map (fun name => (name, .base "GroundLiteral")))

private def rule (name : String) (left right : Pattern) (premises : List Premise := []) :
    RewriteRule :=
  { name, typeContext := ruleContext, premises, left, right }

private def sameFields (control : Pattern) : Pattern :=
  configurationPattern (v "state") control (v "frames") (v "input") (v "output")

def sequenceDone : RewriteRule :=
  rule "sequence-done"
    (sameFields (sequencePattern (expressionPattern []) (v "answers")))
    (sameFields (returnedPattern (v "answers")))

def sequenceEnter : RewriteRule :=
  rule "sequence-enter"
    (sameFields (sequencePattern (expressionPattern [v "first"] (some "pendingTail"))
      (v "answers")))
    (configurationPattern (v "state") (v "first")
      (expressionPattern [framePattern "petta-frame-sequence-v1"
        [expressionPattern [] (some "pendingTail"), v "answers"]] (some "framesTail"))
      (v "input") (v "output"))
    [query "petta-list-vector" [v "frames", v "framesTail"]]

def construct : RewriteRule :=
  rule "construct"
    (sameFields (argumentsPattern (v "bindings") (symbolPattern "petta-target-data-v1")
      (expressionPattern []) (v "values") (v "position")))
    (sameFields (returnedPattern (expressionPattern [v "values"])))

private def ioArguments (head : String) (values : Pattern) : Pattern :=
  argumentsPattern (v "bindings") (functionPattern (stringPattern head))
    (expressionPattern []) values (v "position")

def readEnd : RewriteRule :=
  rule "read-end"
    (configurationPattern (v "state") (ioArguments "readln!" (expressionPattern []))
      (v "frames") (expressionPattern []) (v "output"))
    (configurationPattern (v "state")
      (returnedPattern (expressionPattern [symbolPattern "end_of_file"]))
      (v "frames") (expressionPattern []) (v "output"))

def readLine : RewriteRule :=
  rule "read-line"
    (configurationPattern (v "state") (ioArguments "readln!" (expressionPattern []))
      (v "frames") (expressionPattern [v "first"] (some "inputTail")) (v "output"))
    (configurationPattern (v "state") (returnedPattern (expressionPattern [v "first"]))
      (v "frames") (expressionPattern [] (some "inputTail")) (v "output"))

def printValue : RewriteRule :=
  rule "print"
    (sameFields (ioArguments "println!" (expressionPattern [v "value"])))
    (configurationPattern (v "state")
      (returnedPattern (expressionPattern [OSLFCore.Bridge.GroundData.encode (Effects.boolean true)]))
      (v "frames") (v "input") (v "combined"))
    [query "petta-list-append" [v "output", expressionPattern [v "value"], v "combined"]]

def evaluateCode : RewriteRule :=
  rule "evaluate-code"
    (sameFields (ioArguments "eval" (expressionPattern [v "code"])))
    (sameFields (evaluatePattern (expressionPattern []) (v "code")))

private def ioFault (head : String) : Pattern :=
  faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern head])

def readBad : RewriteRule :=
  rule "read-bad" (sameFields (ioArguments "readln!" (v "values")))
    (sameFields (ioFault "readln!")) [query "petta-list-nonempty" [v "values"]]

def printBad : RewriteRule :=
  rule "print-bad" (sameFields (ioArguments "println!" (v "values")))
    (sameFields (ioFault "println!")) [query "petta-list-not-singleton" [v "values"]]

def evalBad : RewriteRule :=
  rule "eval-bad" (sameFields (ioArguments "eval" (v "values")))
    (sameFields (ioFault "eval")) [query "petta-list-not-singleton" [v "values"]]

private def finishedArguments : Pattern :=
  argumentsPattern (v "bindings") (functionPattern (v "head"))
    (expressionPattern []) (v "values") (v "position")

def primitive : RewriteRule :=
  rule "primitive" (sameFields finishedArguments)
    (configurationPattern (v "after") (returnedPattern (v "answers"))
      (v "frames") (v "input") (v "output"))
    [query "petta-native-head" [v "head"],
      query "petta-primitive-success" [v "state", v "head", v "values", v "after", v "answers"]]

def primitiveFault : RewriteRule :=
  rule "primitive-fault" (sameFields finishedArguments)
    (sameFields (faultPattern (v "reason")))
    [query "petta-native-head" [v "head"],
      query "petta-primitive-fault" [v "state", v "head", v "values", v "reason"]]

def equations : RewriteRule :=
  rule "equations" (sameFields finishedArguments)
    (sameFields (sequencePattern (v "successors") (expressionPattern [])))
    [query "petta-equation-head" [v "head"],
      query "petta-clauses" [v "head", v "values", v "successors"]]

private def pendingArguments : Pattern :=
  argumentsPattern (v "bindings") (v "target")
    (expressionPattern [v "first"] (some "pendingTail")) (v "values") (v "position")

private def argumentFrame : Pattern :=
  framePattern "petta-frame-argument-v1" [v "bindings", v "target",
    expressionPattern [] (some "pendingTail"), v "values", v "position"]

private def argumentTarget (control : Pattern) : Pattern :=
  configurationPattern (v "state") control
    (expressionPattern [argumentFrame] (some "framesTail")) (v "input") (v "output")

def rawArgument : RewriteRule :=
  rule "raw-argument" (sameFields pendingArguments)
    (argumentTarget (returnedPattern (expressionPattern [v "substituted"])))
    [query "petta-raw-demand" [v "target", v "position"],
      query "petta-substitute" [v "bindings", v "first", v "substituted"],
      query "petta-list-vector" [v "frames", v "framesTail"]]

def evaluatedArgument : RewriteRule :=
  rule "evaluated-argument" (sameFields pendingArguments)
    (argumentTarget (evaluatePattern (v "bindings") (v "first")))
    [query "petta-evaluated-demand" [v "target", v "position"],
      query "petta-list-vector" [v "frames", v "framesTail"]]

def valueVariable : RewriteRule :=
  rule "value-variable"
    (sameFields (evaluatePattern (v "bindings")
      (.apply "ground-atom-variable-v1" [v "spelling"])))
    (sameFields (returnedPattern (expressionPattern [v "substituted"])))
    [query "petta-substitute" [v "bindings",
      .apply "ground-atom-variable-v1" [v "spelling"], v "substituted"]]

def symbol : RewriteRule :=
  rule "symbol"
    (sameFields (evaluatePattern (v "bindings")
      (.apply "ground-atom-symbol-v1" [v "spelling"])))
    (sameFields (returnedPattern
      (expressionPattern [.apply "ground-atom-symbol-v1" [v "spelling"]])))

def grounded : RewriteRule :=
  rule "grounded" (sameFields (evaluatePattern (v "bindings") (v "value")))
    (sameFields (returnedPattern (expressionPattern [v "value"])))
    [query "petta-grounded" [v "value"]]

private def controlExpression (head : String) (arguments : List Pattern) : Pattern :=
  expressionPattern (symbolPattern head :: arguments)

private def pushFrame (control frame : Pattern) : Pattern :=
  configurationPattern (v "state") control
    (expressionPattern [frame] (some "framesTail")) (v "input") (v "output")

def letEnter : RewriteRule :=
  rule "let-enter"
    (sameFields (evaluatePattern (v "bindings")
      (controlExpression "let" [v "pattern", v "value", v "body"])))
    (pushFrame (evaluatePattern (v "bindings") (v "value"))
      (framePattern "petta-frame-bind-v1" [v "bindings", v "pattern", v "body"]))
    [query "petta-list-vector" [v "frames", v "framesTail"]]

private def letStarSource : Pattern :=
  sameFields (evaluatePattern (v "bindings")
    (controlExpression "let*" [expressionPattern [] (some "rowsTail"), v "body"]))

def letStar : RewriteRule :=
  rule "let-star" letStarSource (sameFields (evaluatePattern (v "bindings") (v "nested")))
    [query "petta-nested-lets" [expressionPattern [] (some "rowsTail"), v "body", v "nested"]]

def letStarBad : RewriteRule :=
  rule "let-star-bad" letStarSource (sameFields (ioFault "let*"))
    [query "petta-invalid-lets" [expressionPattern [] (some "rowsTail"), v "body"]]

private def caseSource : Pattern :=
  sameFields (evaluatePattern (v "bindings")
    (controlExpression "case" [v "value", expressionPattern [] (some "rowsTail")]))

def caseEnter : RewriteRule :=
  rule "case-enter" caseSource
    (pushFrame (evaluatePattern (v "bindings") (v "value"))
      (framePattern "petta-frame-select-v1" [v "bindings", v "cases"]))
    [query "petta-read-cases" [expressionPattern [] (some "rowsTail"), v "cases"],
      query "petta-list-vector" [v "frames", v "framesTail"]]

def caseBad : RewriteRule :=
  rule "case-bad" caseSource (sameFields (ioFault "case"))
    [query "petta-invalid-cases" [expressionPattern [] (some "rowsTail")]]

def ifEnter : RewriteRule :=
  rule "if-enter"
    (sameFields (evaluatePattern (v "bindings")
      (controlExpression "if" [v "condition", v "yes", v "no"])))
    (pushFrame (evaluatePattern (v "bindings") (v "condition"))
      (framePattern "petta-frame-branch-v1" [v "bindings", v "yes", v "no"]))
    [query "petta-list-vector" [v "frames", v "framesTail"]]

def collapseEnter : RewriteRule :=
  rule "collapse-enter"
    (sameFields (evaluatePattern (v "bindings")
      (controlExpression "collapse" [v "expression"])))
    (pushFrame (evaluatePattern (v "bindings") (v "expression"))
      (symbolPattern "petta-frame-collect-v1"))
    [query "petta-list-vector" [v "frames", v "framesTail"]]

def superposeEnter : RewriteRule :=
  rule "superpose-enter"
    (sameFields (evaluatePattern (v "bindings")
      (controlExpression "superpose" [expressionPattern [] (some "alternativesTail")])))
    (sameFields (sequencePattern (v "successors") (expressionPattern [])))
    [query "petta-evaluate-alternatives" [v "bindings", expressionPattern [] (some "alternativesTail"), v "successors"]]

def emptyEnter : RewriteRule :=
  rule "empty-enter"
    (sameFields (evaluatePattern (v "bindings") (controlExpression "empty" [])))
    (sameFields (returnedPattern (expressionPattern [])))

def quoteEnter : RewriteRule :=
  rule "quote-enter"
    (sameFields (evaluatePattern (v "bindings")
      (controlExpression "quote" [v "expression"])))
    (sameFields (returnedPattern (expressionPattern [v "substituted"])))
    [query "petta-substitute" [v "bindings", v "expression", v "substituted"]]

private def symbolHead : Pattern := .apply "ground-atom-symbol-v1" [v "spelling"]

private def headedExpression : Pattern :=
  expressionPattern [symbolHead] (some "pendingTail")

private def headedSource : Pattern :=
  sameFields (evaluatePattern (v "bindings") headedExpression)

def callEnter : RewriteRule :=
  rule "call-enter" headedSource
    (sameFields (argumentsPattern (v "bindings")
      (functionPattern (.apply "ground-atom-string-v1" [v "spelling"]))
      (expressionPattern [] (some "pendingTail")) (expressionPattern [])
      (OSLFCore.Bridge.GroundData.encode (index 0))))
    [query "petta-not-control" [headedExpression], query "petta-callable" [symbolHead]]

def dataEnter : RewriteRule :=
  rule "data-enter" headedSource
    (sameFields (argumentsPattern (v "bindings") (symbolPattern "petta-target-data-v1")
      headedExpression (expressionPattern []) (OSLFCore.Bridge.GroundData.encode (index 0))))
    [query "petta-not-control" [headedExpression], query "petta-not-callable" [symbolHead]]

def expressionEnter : RewriteRule :=
  rule "expression-enter" (sameFields (evaluatePattern (v "bindings") (v "expression")))
    (sameFields (argumentsPattern (v "bindings") (symbolPattern "petta-target-data-v1")
      (v "expression") (expressionPattern []) (OSLFCore.Bridge.GroundData.encode (index 0))))
    [query "petta-unheaded-expression" [v "expression"]]

private def returnedSource (frame : Pattern) : Pattern :=
  configurationPattern (v "state") (returnedPattern (v "answers"))
    (expressionPattern [frame] (some "framesTail")) (v "input") (v "output")

private def returnedTarget (control : Pattern) : Pattern :=
  configurationPattern (v "state") control
    (expressionPattern [] (some "framesTail")) (v "input") (v "output")

def collapseReturn : RewriteRule :=
  rule "collapse-return" (returnedSource (symbolPattern "petta-frame-collect-v1"))
    (returnedTarget (returnedPattern (expressionPattern [v "answers"])))

def sequenceReturn : RewriteRule :=
  rule "sequence-return"
    (returnedSource (framePattern "petta-frame-sequence-v1" [v "pending", v "collected"]))
    (returnedTarget (sequencePattern (v "pending") (v "combined")))
    [query "petta-list-append" [v "collected", v "answers", v "combined"]]

def argumentReturn : RewriteRule :=
  rule "argument-return"
    (returnedSource (framePattern "petta-frame-argument-v1"
      [v "bindings", v "target", v "pending", v "values", v "position"]))
    (returnedTarget (sequencePattern (v "successors") (expressionPattern [])))
    [query "petta-argument-alternatives" [v "bindings", v "target", v "pending",
      v "values", v "position", v "answers", v "successors"]]

def bindingReturn : RewriteRule :=
  rule "binding-return"
    (returnedSource (framePattern "petta-frame-bind-v1" [v "bindings", v "pattern", v "body"]))
    (returnedTarget (sequencePattern (v "successors") (expressionPattern [])))
    [query "petta-binding-alternatives"
      [v "bindings", v "pattern", v "body", v "answers", v "successors"]]

def caseReturn : RewriteRule :=
  rule "case-return"
    (returnedSource (framePattern "petta-frame-select-v1" [v "bindings", v "cases"]))
    (returnedTarget (sequencePattern (v "successors") (expressionPattern [])))
    [query "petta-case-alternatives" [v "bindings", v "cases", v "answers", v "successors"]]

def ifReturn : RewriteRule :=
  rule "if-return"
    (returnedSource (framePattern "petta-frame-branch-v1" [v "bindings", v "yes", v "no"]))
    (returnedTarget (sequencePattern (v "successors") (expressionPattern [])))
    [query "petta-branch-alternatives"
      [v "bindings", v "yes", v "no", v "answers", v "successors"]]

def rules : List RewriteRule :=
  [sequenceDone, sequenceEnter, construct, readEnd, readLine, printValue, evaluateCode,
    readBad, printBad, evalBad, primitive, primitiveFault, equations, rawArgument,
    evaluatedArgument, valueVariable, symbol, grounded, letEnter, letStar, letStarBad,
    caseEnter, caseBad, ifEnter, collapseEnter, superposeEnter, emptyEnter, quoteEnter,
    callEnter, dataEnter, expressionEnter, collapseReturn, sequenceReturn,
    argumentReturn, bindingReturn, caseReturn, ifReturn]

def language : LanguageDef :=
  { OSLFCore.Bridge.GroundData.dataLanguage with name := "PeTTaConfigurations", rewrites := rules }

theorem rule_count : rules.length = 37 := rfl

theorem no_authored_equations : language.equations = [] := rfl

theorem equation_free : language.isEquationFree = true := by decide

theorem nonrecursive_rules : ∀ rewrite ∈ language.rewrites,
    Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises rewrite.premises := by
  intro rewrite member
  simp only [language, rules, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals repeat' constructor

private def atom? (pattern : Pattern) : Option Atom := OSLFCore.Bridge.GroundData.decode pattern

private def list? (pattern : Pattern) : Option (List Atom) := do
  match ← atom? pattern with
  | .expression values => some values
  | _ => none

private def text? (pattern : Pattern) : Option String := do
  match ← atom? pattern with
  | .grounded (.string name) => some name
  | _ => none

private def symbol? (pattern : Pattern) : Option String := do
  match ← atom? pattern with
  | .symbol name => some name
  | _ => none

private def bindings? (pattern : Pattern) := atom? pattern >>= readBindings

private def cases? (pattern : Pattern) := atom? pattern >>= ConfigurationEncoding.readCases

private def target? (pattern : Pattern) := atom? pattern >>= readTarget

private def index? (pattern : Pattern) := atom? pattern >>= readIndex

private def encoded (atom : Atom) : Pattern := OSLFCore.Bridge.GroundData.encode atom

private def encodedList (values : List Atom) : Pattern := encoded (.expression values)

private def encodedControls (controls : List Eval.Control) : Pattern :=
  encodedList (controlsData controls)

private def row (arguments : List Pattern) (accepted : Bool) : List (List Pattern) :=
  if accepted then [arguments] else []

private def results (computation : Option (List Pattern)) : List (List Pattern) :=
  computation.toList

/-- Read the finite store and the names physically present in its cell rows. -/
private def store? (pattern : Pattern) : Option (Effects.State × List String) := do
  let value ← atom? pattern
  let state ← readState value
  match value with
  | .expression [_, _, _, .expression cells] =>
      return (state, (← readCells cells).map Prod.fst)
  | _ => none

/-- A finite catalog of the data operations used in the authored rules.
No branch calls `Eval.step`, a fuelled runner, `Transition` or `Runs`. -/
def relationRows (program : SpaceSemantics.Program) (name : String)
    (arguments : List Pattern) : List (List Pattern) :=
  match name, arguments with
  | "petta-list-vector", [source, _] => results do
      let values ← list? source
      return [source, .collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none]
  | "petta-list-append", [first, second, _] => results do
      return [first, second, encodedList ((← list? first) ++ (← list? second))]
  | "petta-list-nonempty", [source] => results do
      let values ← list? source
      if values.isEmpty then none else some [source]
  | "petta-list-not-singleton", [source] => results do
      let values ← list? source
      if values.length = 1 then none else some [source]
  | "petta-native-head", [source] => results do
      let head ← text? source
      if !Eval.ioHead head && StdLib.known head then some [source] else none
  | "petta-equation-head", [source] => results do
      let head ← text? source
      if !Eval.ioHead head && !StdLib.known head then some [source] else none
  | "petta-primitive-success", [store, function, inputs, _, _] => results do
      let (state, names) ← store? store
      let head ← text? function
      let values ← list? inputs
      match StdLib.apply state head values with
      | .ok (after, answers) =>
          return [store, function, inputs,
            encoded (stateData after (primitiveCellSupport head values names)), encodedList answers]
      | .error _ => none
  | "petta-primitive-fault", [store, function, inputs, _] => results do
      let (state, _) ← store? store
      let head ← text? function
      let values ← list? inputs
      match StdLib.apply state head values with
      | .ok _ => none
      | .error reason => return [store, function, inputs, encoded (faultData reason)]
  | "petta-clauses", [function, inputs, _] => results do
      return [function, inputs, encodedControls (Eval.clauses program
        (← text? function) (← list? inputs))]
  | "petta-raw-demand", [target, position] => results do
      let destination ← target? target
      let index ← index? position
      match destination with
      | .data => none
      | .function head => if Eval.argumentIsRaw program head index then some [target, position] else none
  | "petta-evaluated-demand", [target, position] => results do
      let destination ← target? target
      let index ← index? position
      match destination with
      | .data => some [target, position]
      | .function head => if Eval.argumentIsRaw program head index then none else some [target, position]
  | "petta-substitute", [bindings, expression, _] => results do
      return [bindings, expression, encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst
        (← bindings? bindings) (← atom? expression))]
  | "petta-grounded", [source] => results do
      match ← atom? source with
      | .grounded _ => some [source]
      | _ => none
  | "petta-nested-lets", [pairs, body, _] => results do
      return [pairs, body, encoded (← Eval.nestedLets (← list? pairs) (← atom? body))]
  | "petta-invalid-lets", [pairs, body] => results do
      if (Eval.nestedLets (← list? pairs) (← atom? body)).isNone then some [pairs, body] else none
  | "petta-read-cases", [rows, _] => results do
      return [rows, encoded (casesData (← Eval.readCases (← list? rows)))]
  | "petta-invalid-cases", [rows] => results do
      if (Eval.readCases (← list? rows)).isNone then some [rows] else none
  | "petta-evaluate-alternatives", [bindings, alternatives, _] => results do
      return [bindings, alternatives, encodedControls
        ((← list? alternatives).map (.evaluate (← bindings? bindings)))]
  | "petta-not-control", [source] => results do
      if DeclarativeSpec.controlForm (← atom? source) then none else some [source]
  | "petta-callable", [source] => results do
      let head ← symbol? source
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
        then some [source] else none
  | "petta-not-callable", [source] => results do
      let head ← symbol? source
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
        then none else some [source]
  | "petta-unheaded-expression", [source] => results do
      match ← atom? source with
      | .expression (.symbol _ :: _) => none
      | .expression _ => some [source]
      | _ => none
  | "petta-argument-alternatives", [bindings, target, pending, values, position, answers, _] =>
      results do
        let captured ← bindings? bindings
        let destination ← target? target
        let remaining ← list? pending
        let collected ← list? values
        let index ← index? position
        let alternatives ← list? answers
        return [bindings, target, pending, values, position, answers,
          encodedControls (alternatives.map fun value =>
            .arguments captured destination remaining (collected ++ [value]) (index + 1))]
  | "petta-binding-alternatives", [bindings, pattern, body, answers, _] => results do
      let captured ← bindings? bindings
      let matchPattern ← atom? pattern
      let expression ← atom? body
      let alternatives ← list? answers
      return [bindings, pattern, body, answers, encodedControls (alternatives.filterMap fun value =>
        (SpaceSemantics.matchBinding captured matchPattern value).map
          fun bound => .evaluate bound expression)]
  | "petta-case-alternatives", [bindings, cases, answers, _] => results do
      let captured ← bindings? bindings
      let rows ← cases? cases
      let alternatives ← list? answers
      return [bindings, cases, answers, encodedControls (alternatives.filterMap fun value =>
        (SpaceSemantics.selectCase captured value rows).map
          fun (bound, body) => .evaluate bound body)]
  | "petta-branch-alternatives", [bindings, yes, no, answers, _] => results do
      let captured ← bindings? bindings
      let ifTrue ← atom? yes
      let ifFalse ← atom? no
      let alternatives ← list? answers
      return [bindings, yes, no, answers, encodedControls (alternatives.map fun value =>
        .evaluate captured (if value == Effects.boolean true then ifTrue else ifFalse))]
  | _, _ => []

def relationEnv (program : SpaceSemantics.Program) : RelationEnv :=
  { tuples := relationRows program }

theorem frontier_iff_generated_step (program : SpaceSemantics.Program) (source target : Pattern) :
    target ∈ rewriteStepWithPremisesUsing (relationEnv program) language source ↔
      (langGSLTUsing (relationEnv program) language).Step source target :=
  mem_rootFrontier_iff_langGSLTUsing_step (relationEnv program) language
    equation_free nonrecursive_rules source target

theorem unknown_relation_refused (program : SpaceSemantics.Program)
    (arguments : List Pattern) : relationRows program "petta-whole-step" arguments = [] := by
  cases arguments <;> rfl

@[simp] private theorem atom?_encoded (atom : Atom) : atom? (encoded atom) = some atom :=
  OSLFCore.Bridge.GroundData.decode_encode atom

@[simp] private theorem list?_encodedList (values : List Atom) :
    list? (encodedList values) = some values := by
  simp [list?, encodedList]

@[simp] private theorem text?_stringPattern (name : String) :
    text? (stringPattern name) = some name := by
  simp [text?, atom?, stringPattern]

@[simp] private theorem symbol?_symbolPattern (name : String) :
    symbol? (symbolPattern name) = some name := by
  simp [symbol?, atom?, symbolPattern]

@[simp] private theorem bindings?_encoded (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) :
    bindings? (encoded (bindingsData bindings)) = some bindings := by
  simp [bindings?]

@[simp] private theorem cases?_encoded (cases : SpaceSemantics.Cases) :
    cases? (encoded (casesData cases)) = some cases := by
  simp [cases?]

@[simp] private theorem target?_encoded (target : Eval.Target) :
    target? (encoded (targetData target)) = some target := by
  simp [target?]

@[simp] private theorem index?_encoded (position : Nat) :
    index? (encoded (index position)) = some position := by
  simp [index?]

private theorem store?_encoded (state : Effects.State) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    store? (encoded (stateData state names)) = some (state, names) := by
  unfold store?
  rw [atom?_encoded]
  change (readState (stateData state names)).bind (fun after =>
    (readCells ((state.cellRows names).map cellData)).bind
      (fun cells => some (after, cells.map Prod.fst))) = some (state, names)
  rw [readState_stateData state names vacant covers, readCells_map]
  simp [NamedSpaces.Store.cellRows, List.map_map, Function.comp_def]

theorem configuration_fields (source : Eval.Configuration) (names : List String) :
    encode source names = configurationPattern (encoded (stateData source.state names))
      (encoded (controlData source.control)) (encodedList (source.frames.map frameData))
      (encodedList source.input) (encodedList source.output) := by
  simp only [encode, configurationData, configurationPattern, taggedPattern,
    expressionPattern, encoded, encodedList, symbolPattern,
    OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]

theorem vector_rows (program : SpaceSemantics.Program) (values : List Atom) (output : Pattern) :
    relationRows program "petta-list-vector" [encodedList values, output] =
      [[encodedList values, .collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none]] := by
  simp [relationRows, results]

private theorem vector_rows_explicit (program : SpaceSemantics.Program)
    (values : List Atom) (output : Pattern) :
    relationRows program "petta-list-vector"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none], output] =
      [[.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        .collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none]] := by
  simpa only [encodedList, encoded, OSLFCore.Bridge.GroundData.encode] using
    vector_rows program values output

theorem append_rows (program : SpaceSemantics.Program) (first second : List Atom)
    (output : Pattern) :
    relationRows program "petta-list-append" [encodedList first, encodedList second, output] =
      [[encodedList first, encodedList second, encodedList (first ++ second)]] := by
  simp [relationRows, results]

theorem substitute_rows (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (expression : Atom) (output : Pattern) :
    relationRows program "petta-substitute" [encoded (bindingsData bindings), encoded expression, output] =
      [[encoded (bindingsData bindings), encoded expression,
        encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings expression)]] := by
  simp [relationRows, results]

private theorem substitute_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (expression : Atom)
    (output : Pattern) :
    relationRows program "petta-substitute"
      [encoded (bindingsData bindings), OSLFCore.Bridge.GroundData.encode expression, output] =
      [[encoded (bindingsData bindings), OSLFCore.Bridge.GroundData.encode expression,
        encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings expression)]] :=
  substitute_rows program bindings expression output

private theorem target_encoded (target : Eval.Target) :
    encoded (targetData target) = match target with
      | .data => symbolPattern "petta-target-data-v1"
      | .function head => functionPattern (stringPattern head) := by
  cases target <;>
    simp only [targetData, encoded, functionPattern, taggedPattern, expressionPattern,
      symbolPattern, stringPattern, text, OSLFCore.Bridge.GroundData.encode,
      OSLFCore.Bridge.GroundData.encodeList]

theorem raw_demand_rows (program : SpaceSemantics.Program) (target : Eval.Target)
    (position : Nat) :
    relationRows program "petta-raw-demand"
      [encoded (targetData target), encoded (index position)] =
      if (match target with
        | .function head => Eval.argumentIsRaw program head position
        | .data => false) then
        [[encoded (targetData target), encoded (index position)]] else [] := by
  cases target <;> simp [relationRows, results]
  split <;> rfl

theorem evaluated_demand_rows (program : SpaceSemantics.Program) (target : Eval.Target)
    (position : Nat) :
    relationRows program "petta-evaluated-demand"
      [encoded (targetData target), encoded (index position)] =
      if (match target with
        | .function head => Eval.argumentIsRaw program head position
        | .data => false) then [] else
        [[encoded (targetData target), encoded (index position)]] := by
  cases target <;> simp [relationRows, results]
  split <;> rfl

private theorem data_raw_demand_rows (program : SpaceSemantics.Program) (position : Nat) :
    relationRows program "petta-raw-demand"
      [(symbolPattern "petta-target-data-v1"), encoded (index position)] = [] := by
  simpa only [target_encoded, Bool.false_eq_true, ↓reduceIte] using raw_demand_rows program .data position

private theorem data_raw_demand_rows_explicit (program : SpaceSemantics.Program) (position : Nat) :
    relationRows program "petta-raw-demand"
      [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "petta-target-data-v1" []]], encoded (index position)] = [] := by
  simpa only [functionPattern, taggedPattern, expressionPattern, symbolPattern_explicit,
    stringPattern_explicit] using data_raw_demand_rows program position

private theorem data_evaluated_demand_rows (program : SpaceSemantics.Program) (position : Nat) :
    relationRows program "petta-evaluated-demand"
      [(symbolPattern "petta-target-data-v1"), encoded (index position)] = [[(symbolPattern "petta-target-data-v1"), encoded (index position)]] := by
  simpa only [target_encoded, Bool.false_eq_true, ↓reduceIte] using evaluated_demand_rows program .data position

private theorem data_evaluated_demand_rows_explicit (program : SpaceSemantics.Program) (position : Nat) :
    relationRows program "petta-evaluated-demand"
      [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "petta-target-data-v1" []]], encoded (index position)] = [[(symbolPattern "petta-target-data-v1"), encoded (index position)]] := by
  simpa only [functionPattern, taggedPattern, expressionPattern, symbolPattern_explicit,
    stringPattern_explicit] using data_evaluated_demand_rows program position

private theorem function_raw_demand_rows (program : SpaceSemantics.Program) (head : String) (position : Nat) :
    relationRows program "petta-raw-demand"
      [(functionPattern (stringPattern head)), encoded (index position)] = if Eval.argumentIsRaw program head position then [[(functionPattern (stringPattern head)), encoded (index position)]] else [] := by
  simpa only [target_encoded, ↓reduceIte] using raw_demand_rows program (.function head) position

private theorem function_raw_demand_rows_explicit (program : SpaceSemantics.Program) (head : String) (position : Nat) :
    relationRows program "petta-raw-demand"
      [.apply "ground-atom-expression-v1" [.collection .vec [
        .apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "petta-target-function-v1" []]],
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]] none], encoded (index position)] = if Eval.argumentIsRaw program head position then [[(functionPattern (stringPattern head)), encoded (index position)]] else [] := by
  simpa only [functionPattern, taggedPattern, expressionPattern, symbolPattern_explicit,
    stringPattern_explicit] using function_raw_demand_rows program head position

private theorem function_evaluated_demand_rows (program : SpaceSemantics.Program) (head : String) (position : Nat) :
    relationRows program "petta-evaluated-demand"
      [(functionPattern (stringPattern head)), encoded (index position)] = if Eval.argumentIsRaw program head position then [] else [[(functionPattern (stringPattern head)), encoded (index position)]] := by
  simpa only [target_encoded, ↓reduceIte] using evaluated_demand_rows program (.function head) position

private theorem function_evaluated_demand_rows_explicit (program : SpaceSemantics.Program) (head : String) (position : Nat) :
    relationRows program "petta-evaluated-demand"
      [.apply "ground-atom-expression-v1" [.collection .vec [
        .apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "petta-target-function-v1" []]],
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]] none], encoded (index position)] = if Eval.argumentIsRaw program head position then [] else [[(functionPattern (stringPattern head)), encoded (index position)]] := by
  simpa only [functionPattern, taggedPattern, expressionPattern, symbolPattern_explicit,
    stringPattern_explicit] using function_evaluated_demand_rows program head position

theorem primitive_success_rows (program : SpaceSemantics.Program) (state after : Effects.State)
    (head : String) (values answers : List Atom) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (returned : StdLib.apply state head values = .ok (after, answers)) (storeOutput answerOutput : Pattern) :
    relationRows program "petta-primitive-success"
      [encoded (stateData state names), stringPattern head, encodedList values, storeOutput, answerOutput] =
      [[encoded (stateData state names), stringPattern head, encodedList values,
        encoded (stateData after (primitiveCellSupport head values names)), encodedList answers]] := by
  simp [relationRows, results, store?_encoded state names vacant covers, returned]

theorem primitive_fault_rows (program : SpaceSemantics.Program) (state : Effects.State)
    (head : String) (values : List Atom) (reason : Effects.Fault) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (failed : StdLib.apply state head values = .error reason) (output : Pattern) :
    relationRows program "petta-primitive-fault"
      [encoded (stateData state names), stringPattern head, encodedList values, output] =
      [[encoded (stateData state names), stringPattern head, encodedList values, encoded (faultData reason)]] := by
  simp [relationRows, results, store?_encoded state names vacant covers, failed]

private theorem primitive_success_rows_explicit (program : SpaceSemantics.Program)
    (state after : Effects.State) (head : String) (values answers : List Atom)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (returned : StdLib.apply state head values = .ok (after, answers))
    (storeOutput answerOutput : Pattern) :
    relationRows program "petta-primitive-success"
      [OSLFCore.Bridge.GroundData.encode (stateData state names),
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        storeOutput, answerOutput] =
      [[OSLFCore.Bridge.GroundData.encode (stateData state names),
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        encoded (stateData after (primitiveCellSupport head values names)), encodedList answers]] := by
  simpa only [encoded, stringPattern_explicit, encodedList, OSLFCore.Bridge.GroundData.encode]
    using primitive_success_rows program state after head values answers names vacant covers
      returned storeOutput answerOutput

private theorem primitive_fault_absent (program : SpaceSemantics.Program)
    (state after : Effects.State) (head : String) (values answers : List Atom)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (returned : StdLib.apply state head values = .ok (after, answers)) (output : Pattern) :
    relationRows program "petta-primitive-fault"
      [OSLFCore.Bridge.GroundData.encode (stateData state names),
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none], output] = [] := by
  have absent : relationRows program "petta-primitive-fault"
      [encoded (stateData state names), stringPattern head, encodedList values, output] = [] := by
    simp [relationRows, results, store?_encoded state names vacant covers, returned]
  simpa only [encoded, stringPattern_explicit, encodedList, OSLFCore.Bridge.GroundData.encode]
    using absent

private theorem primitive_success_absent (program : SpaceSemantics.Program)
    (state : Effects.State) (head : String) (values : List Atom) (reason : Effects.Fault)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (failed : StdLib.apply state head values = .error reason)
    (storeOutput answerOutput : Pattern) :
    relationRows program "petta-primitive-success"
      [OSLFCore.Bridge.GroundData.encode (stateData state names),
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        storeOutput, answerOutput] = [] := by
  have absent : relationRows program "petta-primitive-success"
      [encoded (stateData state names), stringPattern head, encodedList values,
        storeOutput, answerOutput] = [] := by
    simp [relationRows, results, store?_encoded state names vacant covers, failed]
  simpa only [encoded, stringPattern_explicit, encodedList, OSLFCore.Bridge.GroundData.encode]
    using absent

private theorem primitive_fault_rows_explicit (program : SpaceSemantics.Program)
    (state : Effects.State) (head : String) (values : List Atom) (reason : Effects.Fault)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (failed : StdLib.apply state head values = .error reason) (output : Pattern) :
    relationRows program "petta-primitive-fault"
      [OSLFCore.Bridge.GroundData.encode (stateData state names),
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none], output] =
      [[OSLFCore.Bridge.GroundData.encode (stateData state names),
        .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        encoded (faultData reason)]] := by
  simpa only [encoded, stringPattern_explicit, encodedList, OSLFCore.Bridge.GroundData.encode]
    using primitive_fault_rows program state head values reason names vacant covers failed output

private theorem clauses_rows_explicit (program : SpaceSemantics.Program)
    (head : String) (values : List Atom) (output : Pattern) :
    relationRows program "petta-clauses"
      [.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none], output] =
      [[.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        encodedControls (Eval.clauses program head values)]] := by
  have computed : relationRows program "petta-clauses"
      [stringPattern head, encodedList values, output] =
      [[stringPattern head, encodedList values, encodedControls (Eval.clauses program head values)]] := by
    simp [relationRows, results]
  simpa only [stringPattern_explicit, encodedList, encoded, OSLFCore.Bridge.GroundData.encode]
    using computed

theorem native_head_rows (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-native-head" [stringPattern head] =
      if !Eval.ioHead head && StdLib.known head then [[stringPattern head]] else [] := by
  simp [relationRows, results]
  split <;> rfl

theorem equation_head_rows (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-equation-head" [stringPattern head] =
      if !Eval.ioHead head && !StdLib.known head then [[stringPattern head]] else [] := by
  simp [relationRows, results]
  split <;> rfl

theorem nonempty_rows (program : SpaceSemantics.Program) (values : List Atom) :
    relationRows program "petta-list-nonempty" [encodedList values] =
      if values.isEmpty then [] else [[encodedList values]] := by
  simp [relationRows, results]
  split <;> rfl

theorem not_singleton_rows (program : SpaceSemantics.Program) (values : List Atom) :
    relationRows program "petta-list-not-singleton" [encodedList values] =
      if values.length = 1 then [] else [[encodedList values]] := by
  simp [relationRows, results]
  split <;> rfl

private theorem native_head_rows_explicit (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-native-head"
      [.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]] =
      if !Eval.ioHead head && StdLib.known head then
        [[.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]]] else [] := by
  rw [← stringPattern_explicit]
  exact native_head_rows program head

private theorem equation_head_rows_explicit (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-equation-head"
      [.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]] =
      if !Eval.ioHead head && !StdLib.known head then
        [[.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]]] else [] := by
  rw [← stringPattern_explicit]
  exact equation_head_rows program head

private theorem encodedList_fields (values : List Atom) : encodedList values =
    expressionPattern (OSLFCore.Bridge.GroundData.encodeList values) := by
  simp only [encodedList, encoded, expressionPattern, OSLFCore.Bridge.GroundData.encode]

private theorem append_rows_explicit (program : SpaceSemantics.Program)
    (first second : List Atom) (output : Pattern) :
    relationRows program "petta-list-append"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList first) none],
       .apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList second) none], output] =
      [[.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList first) none],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList second) none],
        encodedList (first ++ second)]] := by
  simpa only [encodedList_fields, expressionPattern] using append_rows program first second output

theorem branch_rows (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (yes no : Atom) (answers : List Atom) (output : Pattern) :
    relationRows program "petta-branch-alternatives"
      [encoded (bindingsData bindings), encoded yes, encoded no, encodedList answers, output] =
      [[encoded (bindingsData bindings), encoded yes, encoded no, encodedList answers,
        encodedControls (answers.map fun value => .evaluate bindings
          (if value == Effects.boolean true then yes else no))]] := by
  simp [relationRows, results]

theorem binding_rows (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (pattern body : Atom) (answers : List Atom) (output : Pattern) :
    relationRows program "petta-binding-alternatives"
      [encoded (bindingsData bindings), encoded pattern, encoded body, encodedList answers, output] =
      [[encoded (bindingsData bindings), encoded pattern, encoded body, encodedList answers,
        encodedControls (answers.filterMap fun value =>
          (SpaceSemantics.matchBinding bindings pattern value).map
            fun bound => .evaluate bound body)]] := by
  simp [relationRows, results]

theorem case_rows (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (cases : SpaceSemantics.Cases) (answers : List Atom) (output : Pattern) :
    relationRows program "petta-case-alternatives"
      [encoded (bindingsData bindings), encoded (casesData cases), encodedList answers, output] =
      [[encoded (bindingsData bindings), encoded (casesData cases), encodedList answers,
        encodedControls (answers.filterMap fun value =>
          (SpaceSemantics.selectCase bindings value cases).map
            fun (bound, body) => .evaluate bound body)]] := by
  simp [relationRows, results]

theorem argument_rows (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (target : Eval.Target)
    (pending values answers : List Atom) (position : Nat) (output : Pattern) :
    relationRows program "petta-argument-alternatives"
      [encoded (bindingsData bindings), encoded (targetData target), encodedList pending,
        encodedList values, encoded (index position), encodedList answers, output] =
      [[encoded (bindingsData bindings), encoded (targetData target), encodedList pending,
        encodedList values, encoded (index position), encodedList answers,
        encodedControls (answers.map fun value =>
          .arguments bindings target pending (values ++ [value]) (position + 1))]] := by
  simp [relationRows, results]

private theorem branch_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (yes no : Atom) (answers : List Atom) (output : Pattern) :
    relationRows program "petta-branch-alternatives"
      [encoded (bindingsData bindings), encoded yes, encoded no,
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none], output] =
      [[encoded (bindingsData bindings), encoded yes, encoded no,
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none],
        encodedControls (answers.map fun value => .evaluate bindings
          (if value == Effects.boolean true then yes else no))]] := by
  simpa only [encodedList_fields, expressionPattern] using branch_rows program bindings yes no answers output

private theorem binding_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (pattern body : Atom) (answers : List Atom) (output : Pattern) :
    relationRows program "petta-binding-alternatives"
      [encoded (bindingsData bindings), encoded pattern, encoded body,
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none], output] =
      [[encoded (bindingsData bindings), encoded pattern, encoded body,
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none],
        encodedControls (answers.filterMap fun value =>
          (SpaceSemantics.matchBinding bindings pattern value).map
            fun bound => .evaluate bound body)]] := by
  simpa only [encodedList_fields, expressionPattern] using
    binding_rows program bindings pattern body answers output

private theorem case_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (cases : SpaceSemantics.Cases) (answers : List Atom) (output : Pattern) :
    relationRows program "petta-case-alternatives"
      [encoded (bindingsData bindings), encoded (casesData cases),
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none], output] =
      [[encoded (bindingsData bindings), encoded (casesData cases),
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none],
        encodedControls (answers.filterMap fun value =>
          (SpaceSemantics.selectCase bindings value cases).map
            fun (bound, body) => .evaluate bound body)]] := by
  simpa only [encodedList_fields, expressionPattern] using
    case_rows program bindings cases answers output

private theorem argument_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (target : Eval.Target)
    (pending values answers : List Atom) (position : Nat) (output : Pattern) :
    relationRows program "petta-argument-alternatives"
      [encoded (bindingsData bindings), encoded (targetData target),
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pending) none],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        encoded (index position),
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none], output] =
      [[encoded (bindingsData bindings), encoded (targetData target),
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pending) none],
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList values) none],
        encoded (index position),
        .apply "ground-atom-expression-v1"
          [.collection .vec (OSLFCore.Bridge.GroundData.encodeList answers) none],
        encodedControls (answers.map fun value =>
          .arguments bindings target pending (values ++ [value]) (position + 1))]] := by
  simpa only [encodedList_fields, expressionPattern] using
    argument_rows program bindings target pending values answers position output

private theorem empty_list_nonempty_rows (program : SpaceSemantics.Program) :
    relationRows program "petta-list-nonempty"
      [.apply "ground-atom-expression-v1" [.collection .vec [] none]] = [] := by
  simpa only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, List.isEmpty_nil, ↓reduceIte] using nonempty_rows program []

private theorem singleton_not_singleton_rows (program : SpaceSemantics.Program) (value : Atom) :
    relationRows program "petta-list-not-singleton"
      [.apply "ground-atom-expression-v1" [.collection .vec [encoded value] none]] = [] := by
  simpa only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, encoded, List.length_singleton, ↓reduceIte] using not_singleton_rows program [value]

private theorem nonempty_rows_cons (program : SpaceSemantics.Program) (first : Atom)
    (rest : List Atom) :
    relationRows program "petta-list-nonempty"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encode first :: OSLFCore.Bridge.GroundData.encodeList rest) none]] =
      [[encodedList (first :: rest)]] := by
  simpa only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, encoded, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] using
    nonempty_rows program (first :: rest)

private theorem not_singleton_rows_nil (program : SpaceSemantics.Program) :
    relationRows program "petta-list-not-singleton"
      [.apply "ground-atom-expression-v1" [.collection .vec [] none]] =
      [[encodedList []]] := by
  simpa only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, List.length_nil, Nat.zero_ne_one, ↓reduceIte] using
    not_singleton_rows program []

private theorem not_singleton_rows_many (program : SpaceSemantics.Program)
    (first second : Atom) (rest : List Atom) :
    relationRows program "petta-list-not-singleton"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encode first :: OSLFCore.Bridge.GroundData.encode second ::
          OSLFCore.Bridge.GroundData.encodeList rest) none]] =
      [[encodedList (first :: second :: rest)]] := by
  have many : rest.length + 1 + 1 ≠ 1 := by omega
  simpa only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, List.length_cons, many, ↓reduceIte] using
    not_singleton_rows program (first :: second :: rest)

private theorem append_singleton_rows (program : SpaceSemantics.Program)
    (output : List Atom) (value : Atom) (result : Pattern) :
    relationRows program "petta-list-append"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList output) none],
        .apply "ground-atom-expression-v1" [.collection .vec [OSLFCore.Bridge.GroundData.encode value] none], result] =
      [[encodedList output, encodedList [value], encodedList (output ++ [value])]] := by
  simpa only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, encoded] using append_rows program output [value] result

private theorem singleton_not_singleton_rows_raw (program : SpaceSemantics.Program) (value : Atom) :
    relationRows program "petta-list-not-singleton"
      [.apply "ground-atom-expression-v1"
        [.collection .vec [OSLFCore.Bridge.GroundData.encode value] none]] = [] :=
  singleton_not_singleton_rows program value

private theorem variable_encoded (name : String) : encoded (.var name) =
    .apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode]
  rfl

private theorem variable_grounded_rows_explicit (program : SpaceSemantics.Program)
    (name : String) : relationRows program "petta-grounded"
      [.apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]]] = [] := by
  rw [← variable_encoded]
  simp [relationRows, results]

private theorem variable_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (name : String) : relationRows program "petta-unheaded-expression"
      [.apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]]] = [] := by
  rw [← variable_encoded]
  simp [relationRows, results]

private theorem variable_substitute_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (output : Pattern) : relationRows program "petta-substitute"
      [encoded (bindingsData bindings),
        .apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]], output] =
      [[encoded (bindingsData bindings),
        .apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]],
        encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var name))]] := by
  rw [← variable_encoded]
  exact substitute_rows program bindings (.var name) output

private theorem grounded_rows (program : SpaceSemantics.Program)
    (value : OSLFCore.GroundedValue) :
    relationRows program "petta-grounded" [encoded (.grounded value)] =
      [[encoded (.grounded value)]] := by
  simp [relationRows, results]

private theorem grounded_unheaded_rows (program : SpaceSemantics.Program)
    (value : OSLFCore.GroundedValue) :
    relationRows program "petta-unheaded-expression" [encoded (.grounded value)] = [] := by
  simp [relationRows, results]

private theorem integer_encoded (value : Int) : encoded (.grounded (.int value)) =
    .apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode]
  rfl

private theorem string_encoded (value : String) : encoded (.grounded (.string value)) =
    .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode]
  rfl

private theorem false_encoded : encoded (.grounded (.bool false)) =
    .apply "ground-atom-boolean-false-v1" [] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode]

private theorem true_encoded : encoded (.grounded (.bool true)) =
    .apply "ground-atom-boolean-true-v1" [] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode]

private theorem custom_encoded (typeName data : String) : encoded (.grounded (.custom typeName data)) =
    .apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode]
  rfl

private theorem integer_grounded_rows_explicit (program : SpaceSemantics.Program)
    (value : Int) : relationRows program "petta-grounded" [.apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]]] = [[.apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]]]] := by
  rw [← integer_encoded value]
  exact grounded_rows program (.int value)

private theorem integer_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (value : Int) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]]] = [] := by
  rw [← integer_encoded value]
  exact grounded_unheaded_rows program (.int value)

private theorem string_grounded_rows_explicit (program : SpaceSemantics.Program)
    (value : String) : relationRows program "petta-grounded" [.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]]] = [[.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]]]] := by
  rw [← string_encoded value]
  exact grounded_rows program (.string value)

private theorem string_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (value : String) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]]] = [] := by
  rw [← string_encoded value]
  exact grounded_unheaded_rows program (.string value)

private theorem false_grounded_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-grounded" [.apply "ground-atom-boolean-false-v1" []] = [[.apply "ground-atom-boolean-false-v1" []]] := by
  rw [← false_encoded ]
  exact grounded_rows program (.bool false)

private theorem false_unheaded_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-unheaded-expression" [.apply "ground-atom-boolean-false-v1" []] = [] := by
  rw [← false_encoded ]
  exact grounded_unheaded_rows program (.bool false)

private theorem true_grounded_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-grounded" [.apply "ground-atom-boolean-true-v1" []] = [[.apply "ground-atom-boolean-true-v1" []]] := by
  rw [← true_encoded ]
  exact grounded_rows program (.bool true)

private theorem true_unheaded_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-unheaded-expression" [.apply "ground-atom-boolean-true-v1" []] = [] := by
  rw [← true_encoded ]
  exact grounded_unheaded_rows program (.bool true)

private theorem custom_grounded_rows_explicit (program : SpaceSemantics.Program)
    (typeName data : String) : relationRows program "petta-grounded" [.apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]]] = [[.apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]]]] := by
  rw [← custom_encoded typeName data]
  exact grounded_rows program (.custom typeName data)

private theorem custom_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (typeName data : String) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]]] = [] := by
  rw [← custom_encoded typeName data]
  exact grounded_unheaded_rows program (.custom typeName data)

private theorem let_expression_encoded (pattern value body : Atom) : encoded (.expression [.symbol "let", pattern, value, body]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let" []]], OSLFCore.Bridge.GroundData.encode pattern, OSLFCore.Bridge.GroundData.encode value, OSLFCore.Bridge.GroundData.encode body] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem let_grounded_rows_explicit (program : SpaceSemantics.Program)
    (pattern value body : Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let" []]], OSLFCore.Bridge.GroundData.encode pattern, OSLFCore.Bridge.GroundData.encode value, OSLFCore.Bridge.GroundData.encode body] none]] = [] := by
  rw [← let_expression_encoded pattern value body]
  simp [relationRows, results]

private theorem let_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (pattern value body : Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let" []]], OSLFCore.Bridge.GroundData.encode pattern, OSLFCore.Bridge.GroundData.encode value, OSLFCore.Bridge.GroundData.encode body] none]] = [] := by
  rw [← let_expression_encoded pattern value body]
  simp [relationRows, results]

private theorem let_not_control_rows_explicit (program : SpaceSemantics.Program)
    (pattern value body : Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let" []]], OSLFCore.Bridge.GroundData.encode pattern, OSLFCore.Bridge.GroundData.encode value, OSLFCore.Bridge.GroundData.encode body] none]] = [] := by
  rw [← let_expression_encoded pattern value body]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem if_expression_encoded (condition yes no : Atom) : encoded (.expression [.symbol "if", condition, yes, no]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "if" []]], OSLFCore.Bridge.GroundData.encode condition, OSLFCore.Bridge.GroundData.encode yes, OSLFCore.Bridge.GroundData.encode no] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem if_grounded_rows_explicit (program : SpaceSemantics.Program)
    (condition yes no : Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "if" []]], OSLFCore.Bridge.GroundData.encode condition, OSLFCore.Bridge.GroundData.encode yes, OSLFCore.Bridge.GroundData.encode no] none]] = [] := by
  rw [← if_expression_encoded condition yes no]
  simp [relationRows, results]

private theorem if_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (condition yes no : Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "if" []]], OSLFCore.Bridge.GroundData.encode condition, OSLFCore.Bridge.GroundData.encode yes, OSLFCore.Bridge.GroundData.encode no] none]] = [] := by
  rw [← if_expression_encoded condition yes no]
  simp [relationRows, results]

private theorem if_not_control_rows_explicit (program : SpaceSemantics.Program)
    (condition yes no : Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "if" []]], OSLFCore.Bridge.GroundData.encode condition, OSLFCore.Bridge.GroundData.encode yes, OSLFCore.Bridge.GroundData.encode no] none]] = [] := by
  rw [← if_expression_encoded condition yes no]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem collapse_expression_encoded (expression : Atom) : encoded (.expression [.symbol "collapse", expression]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "collapse" []]], OSLFCore.Bridge.GroundData.encode expression] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem collapse_grounded_rows_explicit (program : SpaceSemantics.Program)
    (expression : Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "collapse" []]], OSLFCore.Bridge.GroundData.encode expression] none]] = [] := by
  rw [← collapse_expression_encoded expression]
  simp [relationRows, results]

private theorem collapse_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (expression : Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "collapse" []]], OSLFCore.Bridge.GroundData.encode expression] none]] = [] := by
  rw [← collapse_expression_encoded expression]
  simp [relationRows, results]

private theorem collapse_not_control_rows_explicit (program : SpaceSemantics.Program)
    (expression : Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "collapse" []]], OSLFCore.Bridge.GroundData.encode expression] none]] = [] := by
  rw [← collapse_expression_encoded expression]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem empty_expression_encoded  : encoded (.expression [.symbol "empty"]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "empty" []]]] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem empty_grounded_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "empty" []]]] none]] = [] := by
  rw [← empty_expression_encoded ]
  simp [relationRows, results]

private theorem empty_unheaded_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "empty" []]]] none]] = [] := by
  rw [← empty_expression_encoded ]
  simp [relationRows, results]

private theorem empty_not_control_rows_explicit (program : SpaceSemantics.Program)
     : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "empty" []]]] none]] = [] := by
  rw [← empty_expression_encoded ]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem quote_expression_encoded (expression : Atom) : encoded (.expression [.symbol "quote", expression]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "quote" []]], OSLFCore.Bridge.GroundData.encode expression] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem quote_grounded_rows_explicit (program : SpaceSemantics.Program)
    (expression : Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "quote" []]], OSLFCore.Bridge.GroundData.encode expression] none]] = [] := by
  rw [← quote_expression_encoded expression]
  simp [relationRows, results]

private theorem quote_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (expression : Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "quote" []]], OSLFCore.Bridge.GroundData.encode expression] none]] = [] := by
  rw [← quote_expression_encoded expression]
  simp [relationRows, results]

private theorem quote_not_control_rows_explicit (program : SpaceSemantics.Program)
    (expression : Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "quote" []]], OSLFCore.Bridge.GroundData.encode expression] none]] = [] := by
  rw [← quote_expression_encoded expression]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem let_star_expression_encoded (pairs : List Atom) (body : Atom) : encoded (.expression [.symbol "let*", .expression pairs, body]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let*" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pairs) none], OSLFCore.Bridge.GroundData.encode body] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem let_star_grounded_rows_explicit (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let*" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pairs) none], OSLFCore.Bridge.GroundData.encode body] none]] = [] := by
  rw [← let_star_expression_encoded pairs body]
  simp [relationRows, results]

private theorem let_star_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let*" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pairs) none], OSLFCore.Bridge.GroundData.encode body] none]] = [] := by
  rw [← let_star_expression_encoded pairs body]
  simp [relationRows, results]

private theorem let_star_not_control_rows_explicit (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let*" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pairs) none], OSLFCore.Bridge.GroundData.encode body] none]] = [] := by
  rw [← let_star_expression_encoded pairs body]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem case_expression_encoded (value : Atom) (rows : List Atom) : encoded (.expression [.symbol "case", value, .expression rows]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "case" []]], OSLFCore.Bridge.GroundData.encode value, .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList rows) none]] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem case_grounded_rows_explicit (program : SpaceSemantics.Program)
    (value : Atom) (rows : List Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "case" []]], OSLFCore.Bridge.GroundData.encode value, .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList rows) none]] none]] = [] := by
  rw [← case_expression_encoded value rows]
  simp [relationRows, results]

private theorem case_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (value : Atom) (rows : List Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "case" []]], OSLFCore.Bridge.GroundData.encode value, .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList rows) none]] none]] = [] := by
  rw [← case_expression_encoded value rows]
  simp [relationRows, results]

private theorem case_not_control_rows_explicit (program : SpaceSemantics.Program)
    (value : Atom) (rows : List Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "case" []]], OSLFCore.Bridge.GroundData.encode value, .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList rows) none]] none]] = [] := by
  rw [← case_expression_encoded value rows]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem superpose_expression_encoded (alternatives : List Atom) : encoded (.expression [.symbol "superpose", .expression alternatives]) =
    .apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "superpose" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList alternatives) none]] none] := by
  simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl

private theorem superpose_grounded_rows_explicit (program : SpaceSemantics.Program)
    (alternatives : List Atom) : relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "superpose" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList alternatives) none]] none]] = [] := by
  rw [← superpose_expression_encoded alternatives]
  simp [relationRows, results]

private theorem superpose_unheaded_rows_explicit (program : SpaceSemantics.Program)
    (alternatives : List Atom) : relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "superpose" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList alternatives) none]] none]] = [] := by
  rw [← superpose_expression_encoded alternatives]
  simp [relationRows, results]

private theorem superpose_not_control_rows_explicit (program : SpaceSemantics.Program)
    (alternatives : List Atom) : relationRows program "petta-not-control" [.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "superpose" []]], .apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList alternatives) none]] none]] = [] := by
  rw [← superpose_expression_encoded alternatives]
  simp [relationRows, results, DeclarativeSpec.controlForm]

private theorem nested_lets_rows (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) (output : Pattern) :
    relationRows program "petta-nested-lets" [encodedList pairs, encoded body, output] =
      (Eval.nestedLets pairs body).toList.map
        (fun nested => [encodedList pairs, encoded body, encoded nested]) := by
  cases built : Eval.nestedLets pairs body <;> simp [relationRows, results, built]

private theorem nested_lets_rows_explicit (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) (output : Pattern) :
    relationRows program "petta-nested-lets"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pairs) none],
        OSLFCore.Bridge.GroundData.encode body, output] =
      (Eval.nestedLets pairs body).toList.map
        (fun nested => [encodedList pairs, encoded body, encoded nested]) := by
  simpa only [encodedList, encoded, OSLFCore.Bridge.GroundData.encode] using
    nested_lets_rows program pairs body output

private theorem invalid_lets_rows (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) :
    relationRows program "petta-invalid-lets" [encodedList pairs, encoded body] =
      if (Eval.nestedLets pairs body).isNone then [[encodedList pairs, encoded body]] else [] := by
  cases built : Eval.nestedLets pairs body <;> simp [relationRows, results, built]

private theorem invalid_lets_rows_explicit (program : SpaceSemantics.Program)
    (pairs : List Atom) (body : Atom) :
    relationRows program "petta-invalid-lets"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList pairs) none],
        OSLFCore.Bridge.GroundData.encode body] =
      if (Eval.nestedLets pairs body).isNone then [[encodedList pairs, encoded body]] else [] := by
  simpa only [encodedList, encoded, OSLFCore.Bridge.GroundData.encode] using
    invalid_lets_rows program pairs body

private theorem read_cases_rows (program : SpaceSemantics.Program)
    (rows : List Atom) (output : Pattern) :
    relationRows program "petta-read-cases" [encodedList rows, output] =
      (Eval.readCases rows).toList.map
        (fun cases => [encodedList rows, encoded (casesData cases)]) := by
  cases parsed : Eval.readCases rows <;> simp [relationRows, results, parsed]

private theorem read_cases_rows_explicit (program : SpaceSemantics.Program)
    (rows : List Atom) (output : Pattern) :
    relationRows program "petta-read-cases"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList rows) none], output] =
      (Eval.readCases rows).toList.map
        (fun cases => [encodedList rows, encoded (casesData cases)]) := by
  simpa only [encodedList, encoded, OSLFCore.Bridge.GroundData.encode] using
    read_cases_rows program rows output

private theorem invalid_cases_rows (program : SpaceSemantics.Program)
    (rows : List Atom) :
    relationRows program "petta-invalid-cases" [encodedList rows] =
      if (Eval.readCases rows).isNone then [[encodedList rows]] else [] := by
  cases parsed : Eval.readCases rows <;> simp [relationRows, results, parsed]

private theorem invalid_cases_rows_explicit (program : SpaceSemantics.Program)
    (rows : List Atom) :
    relationRows program "petta-invalid-cases"
      [.apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList rows) none]] =
      if (Eval.readCases rows).isNone then [[encodedList rows]] else [] := by
  simpa only [encodedList, encoded, OSLFCore.Bridge.GroundData.encode] using
    invalid_cases_rows program rows

private theorem evaluate_alternatives_rows (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (alternatives : List Atom) (output : Pattern) :
    relationRows program "petta-evaluate-alternatives"
      [encoded (bindingsData bindings), encodedList alternatives, output] =
      [[encoded (bindingsData bindings), encodedList alternatives,
        encodedControls (alternatives.map (.evaluate bindings))]] := by
  simp [relationRows, results]

private theorem evaluate_alternatives_rows_explicit (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (alternatives : List Atom) (output : Pattern) :
    relationRows program "petta-evaluate-alternatives"
      [encoded (bindingsData bindings), .apply "ground-atom-expression-v1"
        [.collection .vec (OSLFCore.Bridge.GroundData.encodeList alternatives) none], output] =
      [[encoded (bindingsData bindings), encodedList alternatives,
        encodedControls (alternatives.map (.evaluate bindings))]] := by
  simpa only [encodedList, encoded, OSLFCore.Bridge.GroundData.encode] using
    evaluate_alternatives_rows program bindings alternatives output

private theorem symbol_grounded_rows (program : SpaceSemantics.Program) (name : String) :
    relationRows program "petta-grounded" [symbolPattern name] = [] := by
  simp [relationRows, results, atom?, symbolPattern]

private theorem symbol_unheaded_rows (program : SpaceSemantics.Program) (name : String) :
    relationRows program "petta-unheaded-expression" [symbolPattern name] = [] := by
  simp [relationRows, results, atom?, symbolPattern]

private theorem symbol_grounded_rows_explicit (program : SpaceSemantics.Program) (name : String) :
    relationRows program "petta-grounded"
      [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply name []]]] = [] := by
  rw [← symbolPattern_explicit]
  exact symbol_grounded_rows program name

private theorem symbol_unheaded_rows_explicit (program : SpaceSemantics.Program) (name : String) :
    relationRows program "petta-unheaded-expression"
      [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply name []]]] = [] := by
  rw [← symbolPattern_explicit]
  exact symbol_unheaded_rows program name

theorem symbol_rule_execution (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) (name : String) :
    applyRuleWithPremisesUsing (relationEnv program) language symbol
      (configurationPattern state (evaluatePattern bindings (symbolPattern name)) frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [symbolPattern name])) frames input output] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings,
    symbol, rule, sameFields, configurationPattern, evaluatePattern, returnedPattern,
    taggedPattern, expressionPattern, symbolPattern_explicit, v,
    matchPattern, matchArgs, mergeBindings, applyBindings]

theorem sequence_done_rule_execution (program : SpaceSemantics.Program)
    (state answers frames input output : Pattern) :
    applyRuleWithPremisesUsing (relationEnv program) language sequenceDone
      (configurationPattern state (sequencePattern (expressionPattern []) answers) frames input output) =
      [configurationPattern state (returnedPattern answers) frames input output] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, sequenceDone, rule, sameFields, configurationPattern,
    sequencePattern, returnedPattern, taggedPattern, expressionPattern,
    symbolPattern_explicit, v, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem construct_rule_execution (program : SpaceSemantics.Program)
    (state bindings values position frames input output : Pattern) :
    applyRuleWithPremisesUsing (relationEnv program) language construct
      (configurationPattern state
        (argumentsPattern bindings (symbolPattern "petta-target-data-v1")
          (expressionPattern []) values position) frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [values])) frames input output] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, construct, rule, sameFields, configurationPattern,
    argumentsPattern, returnedPattern, taggedPattern, expressionPattern,
    symbolPattern_explicit, v, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem evaluate_code_rule_execution (program : SpaceSemantics.Program)
    (state bindings code position frames input output : Pattern) :
    applyRuleWithPremisesUsing (relationEnv program) language evaluateCode
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "eval"))
          (expressionPattern []) (expressionPattern [code]) position) frames input output) =
      [configurationPattern state (evaluatePattern (expressionPattern []) code) frames input output] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, evaluateCode, ioArguments, rule, sameFields, configurationPattern,
    argumentsPattern, functionPattern, evaluatePattern, taggedPattern, expressionPattern,
    symbolPattern_explicit, stringPattern_explicit, v,
    matchPattern, matchArgs, mergeBindings, applyBindings]

theorem empty_rule_execution (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) :
    applyRuleWithPremisesUsing (relationEnv program) language emptyEnter
      (configurationPattern state
        (evaluatePattern bindings (controlExpression "empty" [])) frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [])) frames input output] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, emptyEnter, controlExpression, rule, sameFields, configurationPattern,
    evaluatePattern, returnedPattern, taggedPattern, expressionPattern,
    symbolPattern_explicit, v, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem evaluate_encoded (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (expression : Atom) :
    encoded (controlData (.evaluate bindings expression)) =
      evaluatePattern (encoded (bindingsData bindings)) (encoded expression) := by
  simp only [controlData, encoded, evaluatePattern, taggedPattern, expressionPattern,
    symbolPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]

private theorem returned_encoded (answers : List Atom) :
    encoded (controlData (.returned answers)) = returnedPattern (encodedList answers) := by
  simp only [controlData, encoded, encodedList, returnedPattern, taggedPattern,
    expressionPattern, symbolPattern, OSLFCore.Bridge.GroundData.encode,
    OSLFCore.Bridge.GroundData.encodeList]

private theorem sequence_encoded (pending : List Eval.Control) (answers : List Atom) :
    encoded (controlData (.sequence pending answers)) =
      sequencePattern (encodedControls pending) (encodedList answers) := by
  simp only [controlData, encoded, encodedList, encodedControls, sequencePattern,
    taggedPattern, expressionPattern, symbolPattern, OSLFCore.Bridge.GroundData.encode,
    OSLFCore.Bridge.GroundData.encodeList]

private theorem arguments_encoded (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (target : Eval.Target) (remaining values : List Atom) (position : Nat) :
    encoded (controlData (.arguments bindings target remaining values position)) =
      argumentsPattern (encoded (bindingsData bindings)) (encoded (targetData target))
        (encodedList remaining) (encodedList values) (encoded (index position)) := by
  simp only [controlData, encoded, encodedList, argumentsPattern, taggedPattern,
    expressionPattern, symbolPattern, OSLFCore.Bridge.GroundData.encode,
    OSLFCore.Bridge.GroundData.encodeList]

private theorem fault_encoded (reason : Effects.Fault) :
    encoded (controlData (.fault reason)) = faultPattern (encoded (faultData reason)) := by
  simp only [controlData, encoded, faultPattern, taggedPattern, expressionPattern,
    symbolPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]

private theorem pending_encoded_cons (first : Eval.Control) (rest : List Eval.Control) :
    encodedControls (first :: rest) =
      expressionPattern (encoded (controlData first) ::
        OSLFCore.Bridge.GroundData.encodeList (controlsData rest)) := by
  simp only [encodedControls, controlsData, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList, expressionPattern, encoded]

private theorem frame_encoded (frame : Eval.Frame) :
    encoded (frameData frame) = match frame with
      | .collect => symbolPattern "petta-frame-collect-v1"
      | .bind bindings pattern body => framePattern "petta-frame-bind-v1"
          [encoded (bindingsData bindings), encoded pattern, encoded body]
      | .select bindings cases => framePattern "petta-frame-select-v1"
          [encoded (bindingsData bindings), encoded (casesData cases)]
      | .branch bindings yes no => framePattern "petta-frame-branch-v1"
          [encoded (bindingsData bindings), encoded yes, encoded no]
      | .argument bindings target pending values position => framePattern "petta-frame-argument-v1"
          [encoded (bindingsData bindings), encoded (targetData target), encodedList pending,
            encodedList values, encoded (index position)]
      | .sequence pending collected => framePattern "petta-frame-sequence-v1"
          [encodedControls pending, encodedList collected] := by
  cases frame <;>
    simp only [frameData, encoded, encodedList, encodedControls, framePattern,
      taggedPattern, expressionPattern, symbolPattern, OSLFCore.Bridge.GroundData.encode,
      OSLFCore.Bridge.GroundData.encodeList]

private theorem frames_encoded_cons (first : Eval.Frame) (rest : List Eval.Frame) :
    encodedList ((first :: rest).map frameData) =
      expressionPattern (encoded (frameData first) ::
        OSLFCore.Bridge.GroundData.encodeList (rest.map frameData)) := by
  simp only [List.map_cons, encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, encoded]

private theorem atom_list_encoded_cons (first : Atom) (rest : List Atom) :
    encodedList (first :: rest) =
      expressionPattern (encoded first :: OSLFCore.Bridge.GroundData.encodeList rest) := by
  simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    expressionPattern, encoded]

/-- An actual PeTTa symbol transition is realized by its authored rule. -/
theorem symbol_transition_realized (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String)
    (control : source.control = .evaluate bindings (.symbol name)) :
    encode {source with control := .returned [.symbol name]} names ∈
      rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) := by
  apply List.mem_flatMap.mpr
  refine ⟨symbol, by simp [language, rules], ?_⟩
  rw [configuration_fields, control, evaluate_encoded]
  change encode {source with control := .returned [.symbol name]} names ∈
    applyRuleWithPremisesUsing (relationEnv program) language symbol
      (configurationPattern _ (evaluatePattern _ (symbolPattern name)) _ _ _)
  rw [symbol_rule_execution]
  simp only [List.mem_singleton, configuration_fields, returned_encoded]
  simp only [encodedList, encoded, expressionPattern, symbolPattern,
    OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]

theorem symbol_transition_generated (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String)
    (control : source.control = .evaluate bindings (.symbol name)) :
    (langGSLTUsing (relationEnv program) language).Step (encode source names)
      (encode {source with control := .returned [.symbol name]} names) :=
  (frontier_iff_generated_step program _ _).mp
    (symbol_transition_realized program source names bindings name control)

section InertControls

attribute [local simp] binderFree binderFreeList Eval.ioHead matchRelationArgument Bindings.lookup

attribute [local simp] language rules sequenceDone sequenceEnter construct readEnd readLine
  printValue evaluateCode readBad printBad evalBad primitive primitiveFault equations
  rawArgument evaluatedArgument valueVariable symbol grounded letEnter letStar letStarBad
  caseEnter caseBad ifEnter collapseEnter superposeEnter emptyEnter quoteEnter callEnter
  dataEnter expressionEnter collapseReturn sequenceReturn argumentReturn bindingReturn
  caseReturn ifReturn rule sameFields ioArguments ioFault finishedArguments pendingArguments
  argumentTarget argumentFrame letStarSource caseSource controlExpression pushFrame
  symbolHead headedExpression headedSource returnedSource returnedTarget configurationPattern
  taggedPattern expressionPattern evaluatePattern argumentsPattern sequencePattern returnedPattern
  faultPattern functionPattern framePattern symbolPattern_explicit stringPattern_explicit v query

/-- No authored rule can restart a primitive fault, even with pending frames. -/
theorem fault_inert (program : SpaceSemantics.Program)
    (state reason frames input output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (faultPattern reason) frames input output) = [] := by
  simp +decide [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    matchPattern, matchArgs]

/-- A completed answer has no outgoing edge when the continuation is empty. -/
theorem terminal_inert (program : SpaceSemantics.Program)
    (state answers input output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern answers) (expressionPattern []) input output) = [] := by
  simp +decide [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    matchPattern, matchArgs]

theorem symbol_frontier (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) (name : String) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern bindings (symbolPattern name)) frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [symbolPattern name])) frames input output] := by
  simp +decide [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, symbol_grounded_rows_explicit, symbol_unheaded_rows_explicit]

theorem variable_frontier (program : SpaceSemantics.Program)
    (state frames input output : Pattern)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (evaluatePattern (encoded (bindingsData bindings)) (encoded (.var name))) frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern
        [encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var name))]))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, variable_encoded, variable_substitute_rows_explicit,
    variable_grounded_rows_explicit, variable_unheaded_rows_explicit, matchRelationArgs]

attribute [local simp] integer_encoded string_encoded false_encoded true_encoded custom_encoded
  integer_grounded_rows_explicit integer_unheaded_rows_explicit string_grounded_rows_explicit string_unheaded_rows_explicit false_grounded_rows_explicit false_unheaded_rows_explicit true_grounded_rows_explicit true_unheaded_rows_explicit custom_grounded_rows_explicit custom_unheaded_rows_explicit

set_option maxHeartbeats 1000000 in
/-- Grounded values remain inert for every existing grounded constructor. -/
theorem grounded_frontier (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) (value : OSLFCore.GroundedValue) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern bindings (encoded (.grounded value)))
        frames input output) =
      [configurationPattern state
        (returnedPattern (expressionPattern [encoded (.grounded value)])) frames input output] := by
  cases value <;> try (rename_i boolean; cases (show Bool from boolean))
  all_goals simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, matchRelationArgs]

attribute [local simp] let_expression_encoded let_grounded_rows_explicit let_unheaded_rows_explicit let_not_control_rows_explicit

set_option maxHeartbeats 1000000 in
theorem let_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Pattern) (frames : List Atom) (pattern value body : Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern (bindings) (encoded (.expression [.symbol "let", pattern, value, body])))
        (encodedList frames) input output) =
      [configurationPattern state (evaluatePattern bindings (encoded value)) (expressionPattern (framePattern "petta-frame-bind-v1" [bindings, encoded pattern, encoded body] :: OSLFCore.Bridge.GroundData.encodeList frames)) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, vector_rows_explicit, encodedList_fields, matchRelationArgs]
  simp [encoded]

attribute [local simp] if_expression_encoded if_grounded_rows_explicit if_unheaded_rows_explicit if_not_control_rows_explicit

set_option maxHeartbeats 1000000 in
theorem if_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Pattern) (frames : List Atom) (condition yes no : Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern (bindings) (encoded (.expression [.symbol "if", condition, yes, no])))
        (encodedList frames) input output) =
      [configurationPattern state (evaluatePattern bindings (encoded condition)) (expressionPattern (framePattern "petta-frame-branch-v1" [bindings, encoded yes, encoded no] :: OSLFCore.Bridge.GroundData.encodeList frames)) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, vector_rows_explicit, encodedList_fields, matchRelationArgs]
  simp [encoded]

attribute [local simp] collapse_expression_encoded collapse_grounded_rows_explicit collapse_unheaded_rows_explicit collapse_not_control_rows_explicit

set_option maxHeartbeats 1000000 in
theorem collapse_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Pattern) (frames : List Atom) (expression : Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern (bindings) (encoded (.expression [.symbol "collapse", expression])))
        (encodedList frames) input output) =
      [configurationPattern state (evaluatePattern bindings (encoded expression)) (expressionPattern (symbolPattern "petta-frame-collect-v1" :: OSLFCore.Bridge.GroundData.encodeList frames)) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, vector_rows_explicit, encodedList_fields, matchRelationArgs]
  simp [encoded]

attribute [local simp] empty_expression_encoded empty_grounded_rows_explicit empty_unheaded_rows_explicit empty_not_control_rows_explicit

set_option maxHeartbeats 1000000 in
theorem empty_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings frames : Pattern)  :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern (bindings) (encoded (.expression [.symbol "empty"])))
        frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [])) frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv]

attribute [local simp] quote_expression_encoded quote_grounded_rows_explicit quote_unheaded_rows_explicit quote_not_control_rows_explicit

set_option maxHeartbeats 1000000 in
theorem quote_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (frames : Pattern) (expression : Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (evaluatePattern (encoded (bindingsData bindings)) (encoded (.expression [.symbol "quote", expression])))
        frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings expression)])) frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, substitute_rows_explicit, matchRelationArgs]

attribute [local simp] let_star_expression_encoded let_star_grounded_rows_explicit let_star_unheaded_rows_explicit let_star_not_control_rows_explicit

attribute [local simp] case_expression_encoded case_grounded_rows_explicit case_unheaded_rows_explicit case_not_control_rows_explicit

attribute [local simp] superpose_expression_encoded superpose_grounded_rows_explicit superpose_unheaded_rows_explicit superpose_not_control_rows_explicit

attribute [local simp] nested_lets_rows_explicit invalid_lets_rows_explicit
  read_cases_rows_explicit invalid_cases_rows_explicit evaluate_alternatives_rows_explicit

set_option maxHeartbeats 1000000 in
theorem let_star_frontier (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) (pairs : List Atom) (body : Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (evaluatePattern bindings (encoded (.expression [.symbol "let*", .expression pairs, body])))
        frames input output) =
      match Eval.nestedLets pairs body with
      | some nested => [configurationPattern state (evaluatePattern bindings (encoded nested))
          frames input output]
      | none => [configurationPattern state (ioFault "let*") frames input output] := by
  cases built : Eval.nestedLets pairs body
  all_goals simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, matchRelationArgs, encodedList_fields, built]
  all_goals simp [encoded]

set_option maxHeartbeats 1000000 in
theorem case_frontier (program : SpaceSemantics.Program)
    (state bindings input output : Pattern) (frames : List Atom) (value : Atom) (rows : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (evaluatePattern bindings (encoded (.expression [.symbol "case", value, .expression rows])))
        (encodedList frames) input output) =
      match Eval.readCases rows with
      | some cases => [configurationPattern state (evaluatePattern bindings (encoded value))
          (expressionPattern (framePattern "petta-frame-select-v1"
            [bindings, encoded (casesData cases)] :: OSLFCore.Bridge.GroundData.encodeList frames))
          input output]
      | none => [configurationPattern state (ioFault "case") (encodedList frames) input output] := by
  cases parsed : Eval.readCases rows
  all_goals simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, matchRelationArgs,
    vector_rows_explicit, encodedList_fields, parsed]
  all_goals simp [encoded]

set_option maxHeartbeats 1000000 in
theorem superpose_frontier (program : SpaceSemantics.Program)
    (state frames input output : Pattern)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (alternatives : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (evaluatePattern (encoded (bindingsData bindings))
          (encoded (.expression [.symbol "superpose", .expression alternatives]))) frames input output) =
      [configurationPattern state
        (sequencePattern (encodedControls (alternatives.map (.evaluate bindings))) (expressionPattern []))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, matchRelationArgs, encodedList_fields]

theorem sequence_done_frontier (program : SpaceSemantics.Program)
    (state answers frames input output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (sequencePattern (expressionPattern []) answers) frames input output) =
      [configurationPattern state (returnedPattern answers) frames input output] := by
  simp +decide [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv]

theorem construct_frontier (program : SpaceSemantics.Program)
    (state bindings values position frames input output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (symbolPattern "petta-target-data-v1")
          (expressionPattern []) values position) frames input output) =
      [configurationPattern state (returnedPattern (expressionPattern [values])) frames input output] := by
  simp +decide [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv]

set_option maxHeartbeats 1000000 in
/-- Successful native calls have exactly the authored primitive successor;
I/O and equation rules cannot also contribute answers. -/
theorem primitive_success_frontier (program : SpaceSemantics.Program)
    (state after : Effects.State) (bindings position frames input output : Pattern)
    (head : String) (values answers : List Atom) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (notIO : Eval.ioHead head = false) (native : StdLib.known head = true)
    (returned : StdLib.apply state head values = .ok (after, answers)) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern (encoded (stateData state names))
        (argumentsPattern bindings (functionPattern (stringPattern head))
          (expressionPattern []) (encodedList values) position)
        frames input output) =
      [configurationPattern (encoded (stateData after (primitiveCellSupport head values names)))
        (returnedPattern (encodedList answers)) frames input output] := by
  have notRead : head ≠ "readln!" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  have notEval : head ≠ "eval" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, native_head_rows_explicit, equation_head_rows_explicit,
    primitive_success_rows_explicit program state after head values answers names vacant covers returned,
    primitive_fault_absent program state after head values answers names vacant covers returned,
    encodedList, encoded, OSLFCore.Bridge.GroundData.encode,
    native, notRead, notPrint, notEval, matchRelationArgs]
  split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
/-- A native fault contributes one fault edge and no successful result. -/
theorem primitive_fault_frontier (program : SpaceSemantics.Program)
    (state : Effects.State) (bindings position frames input output : Pattern)
    (head : String) (values : List Atom) (reason : Effects.Fault) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (notIO : Eval.ioHead head = false) (native : StdLib.known head = true)
    (failed : StdLib.apply state head values = .error reason) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern (encoded (stateData state names))
        (argumentsPattern bindings (functionPattern (stringPattern head))
          (expressionPattern []) (encodedList values) position)
        frames input output) =
      [configurationPattern (encoded (stateData state names))
        (faultPattern (encoded (faultData reason))) frames input output] := by
  have notRead : head ≠ "readln!" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  have notEval : head ≠ "eval" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, native_head_rows_explicit, equation_head_rows_explicit,
    primitive_fault_rows_explicit program state head values reason names vacant covers failed,
    primitive_success_absent program state head values reason names vacant covers failed,
    encodedList, encoded, OSLFCore.Bridge.GroundData.encode,
    native, notRead, notPrint, notEval, matchRelationArgs]
  split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
/-- Non-native calls retain the actual equation alternatives in their order. -/
theorem equations_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern)
    (head : String) (values : List Atom)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern head))
          (expressionPattern []) (encodedList values) position)
        frames input output) =
      [configurationPattern state
        (sequencePattern (encodedControls (Eval.clauses program head values))
          (expressionPattern [])) frames input output] := by
  have notRead : head ≠ "readln!" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  have notEval : head ≠ "eval" := by
    intro same
    subst head
    simp [Eval.ioHead] at notIO
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, native_head_rows_explicit, equation_head_rows_explicit, clauses_rows_explicit,
    encodedList, encoded, OSLFCore.Bridge.GroundData.encode,
    notNative, notRead, notPrint, notEval, matchRelationArgs]
  split_ifs <;> simp_all

theorem read_end_frontier (program : SpaceSemantics.Program)
    (state bindings position frames output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "readln!"))
          (expressionPattern []) (expressionPattern []) position)
        frames (expressionPattern []) output) =
      [configurationPattern state
        (returnedPattern (expressionPattern [symbolPattern "end_of_file"]))
        frames (expressionPattern []) output] := by
  simp +decide [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, empty_list_nonempty_rows]

theorem evaluate_code_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern) (code : Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "eval"))
          (expressionPattern []) (expressionPattern [encoded code]) position) frames input output) =
      [configurationPattern state (evaluatePattern (expressionPattern []) (encoded code)) frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, singleton_not_singleton_rows]

theorem read_line_frontier (program : SpaceSemantics.Program)
    (state bindings position frames output : Pattern) (first : Atom) (rest : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "readln!"))
          (expressionPattern []) (expressionPattern []) position)
        frames (encodedList (first :: rest)) output) =
      [configurationPattern state (returnedPattern (expressionPattern [encoded first]))
        frames (encodedList rest) output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, empty_list_nonempty_rows, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList]
  rfl

theorem sequence_enter_frontier (program : SpaceSemantics.Program)
    (state first input output : Pattern) (rest : List Atom) (answers : Pattern) (frames : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (sequencePattern
          (expressionPattern (first :: OSLFCore.Bridge.GroundData.encodeList rest)) answers)
        (encodedList frames) input output) =
      [configurationPattern state first
        (expressionPattern (framePattern "petta-frame-sequence-v1" [encodedList rest, answers] ::
          OSLFCore.Bridge.GroundData.encodeList frames)) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, vector_rows_explicit, encodedList_fields,
    matchRelationArgs]

theorem collapse_return_frontier (program : SpaceSemantics.Program)
    (state answers input output : Pattern) (frames : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern answers)
        (expressionPattern (symbolPattern "petta-frame-collect-v1" :: frames)) input output) =
      [configurationPattern state (returnedPattern (expressionPattern [answers]))
        (expressionPattern frames) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv]

theorem sequence_return_frontier (program : SpaceSemantics.Program)
    (state pending input output : Pattern) (collected answers : List Atom) (frames : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern (encodedList answers))
        (expressionPattern (framePattern "petta-frame-sequence-v1"
          [pending, encodedList collected] :: frames)) input output) =
      [configurationPattern state (sequencePattern pending (encodedList (collected ++ answers)))
        (expressionPattern frames) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, append_rows_explicit, encodedList_fields,
    matchRelationArgs]

theorem if_return_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (yes no : Atom) (answers : List Atom) (frames : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern (encodedList answers))
        (expressionPattern (framePattern "petta-frame-branch-v1"
          [encoded (bindingsData bindings), encoded yes, encoded no] :: frames)) input output) =
      [configurationPattern state
        (sequencePattern (encodedControls (answers.map fun value =>
          .evaluate bindings (if value == Effects.boolean true then yes else no))) (expressionPattern []))
        (expressionPattern frames) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, branch_rows_explicit, encodedList_fields,
    matchRelationArgs]

theorem binding_return_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (pattern body : Atom) (answers : List Atom) (frames : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern (encodedList answers))
        (expressionPattern (framePattern "petta-frame-bind-v1"
          [encoded (bindingsData bindings), encoded pattern, encoded body] :: frames)) input output) =
      [configurationPattern state
        (sequencePattern (encodedControls (answers.filterMap fun value =>
          (SpaceSemantics.matchBinding bindings pattern value).map
            fun bound => .evaluate bound body)) (expressionPattern []))
        (expressionPattern frames) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, binding_rows_explicit, encodedList_fields,
    matchRelationArgs]

theorem case_return_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (cases : SpaceSemantics.Cases) (answers : List Atom) (frames : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern (encodedList answers))
        (expressionPattern (framePattern "petta-frame-select-v1"
          [encoded (bindingsData bindings), encoded (casesData cases)] :: frames)) input output) =
      [configurationPattern state
        (sequencePattern (encodedControls (answers.filterMap fun value =>
          (SpaceSemantics.selectCase bindings value cases).map
            fun (bound, body) => .evaluate bound body)) (expressionPattern []))
        (expressionPattern frames) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, case_rows_explicit, encodedList_fields,
    matchRelationArgs]

set_option maxHeartbeats 1000000 in
theorem argument_return_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (target : Eval.Target) (pending values answers : List Atom) (position : Nat)
    (frames : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state (returnedPattern (encodedList answers))
        (expressionPattern (framePattern "petta-frame-argument-v1"
          [encoded (bindingsData bindings), encoded (targetData target), encodedList pending,
            encodedList values, encoded (index position)] :: frames)) input output) =
      [configurationPattern state
        (sequencePattern (encodedControls (answers.map fun value =>
          .arguments bindings target pending (values ++ [value]) (position + 1)))
          (expressionPattern [])) (expressionPattern frames) input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, argument_rows_explicit, encodedList_fields,
    matchRelationArgs]

set_option maxHeartbeats 1000000 in
/-- Declared argument demand chooses one edge; captured raw values are
substituted once, while a demanded argument enters ordinary evaluation. -/
theorem pending_argument_frontier (program : SpaceSemantics.Program)
    (state input output : Pattern) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (target : Eval.Target) (first : Atom) (rest values : List Atom) (position : Nat)
    (frames : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern (encoded (bindingsData bindings)) (encoded (targetData target))
          (encodedList (first :: rest)) (encodedList values) (encoded (index position)))
        (encodedList frames) input output) =
      [configurationPattern state
        (if (match target with
          | .function head => Eval.argumentIsRaw program head position
          | .data => false) then
          returnedPattern (expressionPattern
            [encoded (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings first)])
        else evaluatePattern (encoded (bindingsData bindings)) (encoded first))
        (expressionPattern (framePattern "petta-frame-argument-v1"
          [encoded (bindingsData bindings), encoded (targetData target), encodedList rest,
            encodedList values, encoded (index position)] ::
          OSLFCore.Bridge.GroundData.encodeList frames)) input output] := by
  cases target with
  | data =>
    rw [target_encoded]
    simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, relationEnv, data_raw_demand_rows_explicit, data_evaluated_demand_rows_explicit,
      vector_rows_explicit, encodedList_fields,
      OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs]
    rfl
  | function head =>
    rw [target_encoded]
    cases demand : Eval.argumentIsRaw program head position with
    | false =>
      simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, relationEnv, function_raw_demand_rows_explicit, function_evaluated_demand_rows_explicit,
        vector_rows_explicit, encodedList_fields,
        OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs, demand]
      split_ifs <;> simp_all <;> rfl
    | true =>
      simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, relationEnv, function_raw_demand_rows_explicit, function_evaluated_demand_rows_explicit,
        substitute_rows_explicit, vector_rows_explicit, encodedList_fields,
        OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs, demand]
      split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
theorem print_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input : Pattern) (value : Atom) (output : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "println!"))
          (expressionPattern []) (expressionPattern [encoded value]) position)
        frames input (encodedList output)) =
      [configurationPattern state
        (returnedPattern (expressionPattern [encoded (Effects.boolean true)]))
        frames input (encodedList (output ++ [value]))] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, singleton_not_singleton_rows_raw, append_singleton_rows,
    encodedList_fields, OSLFCore.Bridge.GroundData.encodeList,
    Effects.boolean, encoded, OSLFCore.Bridge.GroundData.encode, matchRelationArgs]

theorem read_bad_cons_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern) (first : Atom) (rest : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "readln!"))
          (expressionPattern []) (encodedList (first :: rest)) position) frames input output) =
      [configurationPattern state
        (faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern "readln!"] ))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, nonempty_rows_cons, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs]

theorem print_bad_nil_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "println!"))
          (expressionPattern []) (encodedList []) position) frames input output) =
      [configurationPattern state
        (faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern "println!"] ))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, not_singleton_rows_nil, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs]

theorem print_bad_many_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern) (first second : Atom) (rest : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "println!"))
          (expressionPattern []) (encodedList (first :: second :: rest)) position) frames input output) =
      [configurationPattern state
        (faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern "println!"] ))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, not_singleton_rows_many, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs]

theorem eval_bad_nil_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "eval"))
          (expressionPattern []) (encodedList []) position) frames input output) =
      [configurationPattern state
        (faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern "eval"] ))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, not_singleton_rows_nil, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs]

theorem eval_bad_many_frontier (program : SpaceSemantics.Program)
    (state bindings position frames input output : Pattern) (first second : Atom) (rest : List Atom) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (argumentsPattern bindings (functionPattern (stringPattern "eval"))
          (expressionPattern []) (encodedList (first :: second :: rest)) position) frames input output) =
      [configurationPattern state
        (faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern "eval"] ))
        frames input output] := by
  simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relationEnv, native_head_rows_explicit,
    equation_head_rows_explicit, not_singleton_rows_many, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList, matchRelationArgs]

@[local simp] private theorem atom_symbol_explicit (head : String) :
    OSLFCore.Bridge.GroundData.encode (.symbol head) =
      .apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] := by
  simp only [OSLFCore.Bridge.GroundData.encode]
  rfl

@[local simp] private theorem symbol_pattern_explicit (head : String) :
    symbolPattern head =
      .apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] := by
  exact atom_symbol_explicit head

@[local simp] private theorem headed_expression_explicit (head : String) (arguments : List Atom) :
    OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments)) =
      .apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none] := by
  simp only [OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]
  rfl


private theorem matchArgs_no_length (patterns terms : List Pattern)
    (different : patterns.length ≠ terms.length) : matchArgs patterns terms = [] := by
  induction patterns generalizing terms with
  | nil => cases terms <;> simp_all [matchArgs]
  | cons first rest ih =>
      cases terms with
      | nil => simp [matchArgs]
      | cons term terms =>
          have tailLength : rest.length ≠ terms.length := by simpa using different
          simp only [matchArgs, ih terms tailLength, List.filterMap_nil]
          exact List.flatMap_eq_nil_iff.mpr (by simp)

private theorem headed_pattern_refused_of_name (name head : String)
    (fields : List Pattern) (arguments : List Atom) (different : name ≠ head) :
    matchPattern (expressionPattern (symbolPattern name :: fields))
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  simp [expressionPattern, matchPattern, matchArgs, different]

private theorem encodeList_length (arguments : List Atom) :
    (OSLFCore.Bridge.GroundData.encodeList arguments).length = arguments.length := by
  induction arguments with
  | nil => simp [OSLFCore.Bridge.GroundData.encodeList]
  | cons first rest ih => simp [OSLFCore.Bridge.GroundData.encodeList, ih]

private theorem headed_pattern_refused_of_length (name head : String)
    (fields : List Pattern) (arguments : List Atom)
    (different : fields.length ≠ arguments.length) :
    matchPattern (expressionPattern (symbolPattern name :: fields))
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  have vectorDifferent : (symbolPattern name :: fields).length ≠
      (OSLFCore.Bridge.GroundData.encode (.symbol head) ::
        OSLFCore.Bridge.GroundData.encodeList arguments).length := by
    simpa only [List.length_cons, encodeList_length, ne_eq, Nat.add_right_cancel_iff] using different
  have refused := matchArgs_no_length
    (symbolPattern name :: fields)
    (OSLFCore.Bridge.GroundData.encode (.symbol head) ::
      OSLFCore.Bridge.GroundData.encodeList arguments) vectorDifferent
  simp only [atom_symbol_explicit, symbol_pattern_explicit] at refused
  simp [expressionPattern, matchPattern, matchArgs, refused]

set_option maxHeartbeats 1000000 in
theorem ordinary_let_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "let", .fvar "pattern", .fvar "value", .fvar "body"])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "let"
  · subst head
    by_cases arity : arguments.length = 3
    · obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp arity
      simp [DeclarativeSpec.controlForm] at ordinary
    · exact headed_pattern_refused_of_length "let" "let" [.fvar "pattern", .fvar "value", .fvar "body"] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "let" head [.fvar "pattern", .fvar "value", .fvar "body"] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_if_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "if", .fvar "condition", .fvar "yes", .fvar "no"])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "if"
  · subst head
    by_cases arity : arguments.length = 3
    · obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp arity
      simp [DeclarativeSpec.controlForm] at ordinary
    · exact headed_pattern_refused_of_length "if" "if" [.fvar "condition", .fvar "yes", .fvar "no"] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "if" head [.fvar "condition", .fvar "yes", .fvar "no"] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_collapse_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "collapse", .fvar "expression"])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "collapse"
  · subst head
    by_cases arity : arguments.length = 1
    · obtain ⟨one, rfl⟩ := List.length_eq_one_iff.mp arity
      simp [DeclarativeSpec.controlForm] at ordinary
    · exact headed_pattern_refused_of_length "collapse" "collapse" [.fvar "expression"] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "collapse" head [.fvar "expression"] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_empty_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "empty"])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "empty"
  · subst head
    by_cases arity : arguments.length = 0
    · have empty : arguments = [] := List.length_eq_zero_iff.mp arity
      subst arguments
      simp [DeclarativeSpec.controlForm] at ordinary
    · exact headed_pattern_refused_of_length "empty" "empty" [] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "empty" head [] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_quote_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "quote", .fvar "expression"])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "quote"
  · subst head
    by_cases arity : arguments.length = 1
    · obtain ⟨one, rfl⟩ := List.length_eq_one_iff.mp arity
      simp [DeclarativeSpec.controlForm] at ordinary
    · exact headed_pattern_refused_of_length "quote" "quote" [.fvar "expression"] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "quote" head [.fvar "expression"] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_let_star_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "let*", expressionPattern [] (some "rowsTail"), .fvar "body"])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "let*"
  · subst head
    by_cases arity : arguments.length = 2
    · obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp arity
      cases first with
      | expression rows => simp [DeclarativeSpec.controlForm] at ordinary
      | var x => simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
      | symbol x => simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
      | grounded value =>
          cases value <;> try cases ‹Bool›
          all_goals simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
    · exact headed_pattern_refused_of_length "let*" "let*" [expressionPattern [] (some "rowsTail"), .fvar "body"] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "let*" head [expressionPattern [] (some "rowsTail"), .fvar "body"] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_case_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "case", .fvar "value", expressionPattern [] (some "rowsTail")])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "case"
  · subst head
    by_cases arity : arguments.length = 2
    · obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp arity
      cases second with
      | expression rows => simp [DeclarativeSpec.controlForm] at ordinary
      | var x => simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
      | symbol x => simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
      | grounded value =>
          cases value <;> try cases ‹Bool›
          all_goals simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
    · exact headed_pattern_refused_of_length "case" "case" [.fvar "value", expressionPattern [] (some "rowsTail")] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "case" head [.fvar "value", expressionPattern [] (some "rowsTail")] arguments (Ne.symm named)

set_option maxHeartbeats 1000000 in
theorem ordinary_superpose_pattern_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (expressionPattern [symbolPattern "superpose", expressionPattern [] (some "alternativesTail")])
      (OSLFCore.Bridge.GroundData.encode (.expression (.symbol head :: arguments))) = [] := by
  by_cases named : head = "superpose"
  · subst head
    by_cases arity : arguments.length = 1
    · obtain ⟨one, rfl⟩ := List.length_eq_one_iff.mp arity
      cases one with
      | expression rows => simp [DeclarativeSpec.controlForm] at ordinary
      | var x => simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
      | symbol x => simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
      | grounded value =>
          cases value <;> try cases ‹Bool›
          all_goals simp +decide [expressionPattern, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, matchPattern, matchArgs, mergeBindings]
    · exact headed_pattern_refused_of_length "superpose" "superpose" [expressionPattern [] (some "alternativesTail")] arguments (by simpa using Ne.symm arity)
  · exact headed_pattern_refused_of_name "superpose" head [expressionPattern [] (some "alternativesTail")] arguments (Ne.symm named)


@[local simp] private theorem decode_headed_expression (head : String) (arguments : List Atom) :
    OSLFCore.Bridge.GroundData.decode (.apply "ground-atom-expression-v1" [.collection .vec
      (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
        OSLFCore.Bridge.GroundData.encodeList arguments) none]) =
      some (.expression (.symbol head :: arguments)) := by
  rw [← headed_expression_explicit]
  exact OSLFCore.Bridge.GroundData.decode_encode _

@[local simp] private theorem decode_symbol_explicit (head : String) :
    OSLFCore.Bridge.GroundData.decode
      (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]) =
        some (.symbol head) := by
  rw [← atom_symbol_explicit]
  exact OSLFCore.Bridge.GroundData.decode_encode _

@[local simp] private theorem ordinary_let_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let" []]], .fvar "pattern", .fvar "value", .fvar "body"] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_let_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_if_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "if" []]], .fvar "condition", .fvar "yes", .fvar "no"] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_if_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_collapse_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "collapse" []]], .fvar "expression"] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_collapse_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_empty_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "empty" []]]] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_empty_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_quote_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "quote" []]], .fvar "expression"] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_quote_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_let_star_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "let*" []]], .apply "ground-atom-expression-v1" [.collection .vec [] (some "rowsTail")], .fvar "body"] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_let_star_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_case_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "case" []]], .fvar "value", .apply "ground-atom-expression-v1" [.collection .vec [] (some "rowsTail")]] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_case_pattern_refused head arguments ordinary

@[local simp] private theorem ordinary_superpose_raw_refused (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    matchPattern (.apply "ground-atom-expression-v1" [.collection .vec [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply "superpose" []]], .apply "ground-atom-expression-v1" [.collection .vec [] (some "alternativesTail")]] none])
      (.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none]) = [] := by
  simpa only [expressionPattern, symbol_pattern_explicit, headed_expression_explicit] using
    ordinary_superpose_pattern_refused head arguments ordinary

private theorem headed_not_control_rows (program : SpaceSemantics.Program)
    (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    relationRows program "petta-not-control"
      [encoded (.expression (.symbol head :: arguments))] =
        [[encoded (.expression (.symbol head :: arguments))]] := by
  simp [relationRows, results, atom?, encoded, ordinary]

private theorem headed_grounded_rows (program : SpaceSemantics.Program)
    (head : String) (arguments : List Atom) :
    relationRows program "petta-grounded" [encoded (.expression (.symbol head :: arguments))] = [] := by
  simp [relationRows, results, atom?, encoded]

private theorem headed_unheaded_rows (program : SpaceSemantics.Program)
    (head : String) (arguments : List Atom) :
    relationRows program "petta-unheaded-expression"
      [encoded (.expression (.symbol head :: arguments))] = [] := by
  simp [relationRows, results, atom?, encoded]

@[local simp] private theorem headed_not_control_rows_raw (program : SpaceSemantics.Program)
    (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    relationRows program "petta-not-control" [(.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none])] = [[(.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none])]]  := by
  rw [← headed_expression_explicit]
  exact headed_not_control_rows program head arguments ordinary

@[local simp] private theorem headed_grounded_rows_raw (program : SpaceSemantics.Program)
    (head : String) (arguments : List Atom)
     :
    relationRows program "petta-grounded" [(.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none])] = [] := by
  rw [← headed_expression_explicit]
  exact headed_grounded_rows program head arguments

@[local simp] private theorem headed_unheaded_rows_raw (program : SpaceSemantics.Program)
    (head : String) (arguments : List Atom)
     :
    relationRows program "petta-unheaded-expression" [(.apply "ground-atom-expression-v1" [.collection .vec
        (.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]] ::
          OSLFCore.Bridge.GroundData.encodeList arguments) none])] = [] := by
  rw [← headed_expression_explicit]
  exact headed_unheaded_rows program head arguments

private theorem callable_rows (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-callable" [symbolPattern head] =
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
        then [[symbolPattern head]] else [] := by
  simp only [relationRows, results, symbol?, atom?, symbolPattern, OSLFCore.Bridge.GroundData.decode_encode]
  change Option.toList (if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
    then some [symbolPattern head] else none) = _
  cases Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head) <;> rfl

private theorem not_callable_rows (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-not-callable" [symbolPattern head] =
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
        then [] else [[symbolPattern head]] := by
  simp only [relationRows, results, symbol?, atom?, symbolPattern, OSLFCore.Bridge.GroundData.decode_encode]
  change Option.toList (if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
    then none else some [symbolPattern head]) = _
  cases Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head) <;> rfl

@[local simp] private theorem callable_rows_raw (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-callable" [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]] =
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
        then [[.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]]] else [] := by
  rw [← symbol_pattern_explicit]
  exact callable_rows program head

@[local simp] private theorem not_callable_rows_raw (program : SpaceSemantics.Program) (head : String) :
    relationRows program "petta-not-callable" [.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]] =
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
        then [] else [[.apply "ground-atom-symbol-v1" [.apply "source-sexpr-atom-v1" [.apply head []]]]] := by
  rw [← symbol_pattern_explicit]
  exact not_callable_rows program head

@[local simp] private theorem index_zero_encoded : encoded (index 0) =
    .apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply "0" []]] := by
  simp only [encoded, index, OSLFCore.Bridge.GroundData.encode]
  rfl

@[local simp] private theorem index_zero_encoded_raw : OSLFCore.Bridge.GroundData.encode (index 0) =
    .apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply "0" []]] := by
  exact index_zero_encoded

set_option maxHeartbeats 2000000 in
theorem ordinary_headed_frontier (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) (head : String) (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (evaluatePattern bindings (encoded (.expression (.symbol head :: arguments)))) frames input output) =
      if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head) then
        [configurationPattern state
          (argumentsPattern bindings (functionPattern (stringPattern head))
            (encodedList arguments) (expressionPattern []) (encoded (index 0))) frames input output]
      else [configurationPattern state
        (argumentsPattern bindings (symbolPattern "petta-target-data-v1")
          (encoded (.expression (.symbol head :: arguments))) (expressionPattern [])
          (encoded (index 0))) frames input output] := by
  cases callable : Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
  all_goals
    have normalizedCallable := callable
    simp [Eval.ioHead] at normalizedCallable
  all_goals simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
    applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    relationEnv, matchRelationArgs, encoded, encodedList_fields, normalizedCallable, ordinary]
  have noEquation : ¬ ∃ row ∈ program.equations, row.head = head := by
    rintro ⟨row, member, same⟩
    exact normalizedCallable.2 row member same
  simp +decide [noEquation, matchRelationArgs, matchPattern, matchArgs, mergeBindings]


@[local simp] private theorem expression_encoded_raw (items : List Atom) :
    OSLFCore.Bridge.GroundData.encode (.expression items) =
      .apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none] := by
  simp only [OSLFCore.Bridge.GroundData.encode]

@[local simp] private theorem decode_expression_raw (items : List Atom) :
    OSLFCore.Bridge.GroundData.decode
      (.apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none]) = some (.expression items) := by
  rw [← expression_encoded_raw]
  exact OSLFCore.Bridge.GroundData.decode_encode (.expression items)

@[local simp] private theorem expression_grounded_rows_raw
    (program : SpaceSemantics.Program) (items : List Atom) :
    relationRows program "petta-grounded"
      [.apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none]] = [] := by
  simp only [relationRows, results, atom?, decode_expression_raw]
  rfl

@[local simp] private theorem expression_not_control_rows_raw
    (program : SpaceSemantics.Program) (items : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression items) = false) :
    relationRows program "petta-not-control"
      [.apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none]] =
      [[.apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none]]] := by
  simp [relationRows, results, atom?, ordinary]

@[local simp] private theorem unheaded_rows_raw
    (program : SpaceSemantics.Program) (items : List Atom)
    (unheaded : ∀ head rest, items ≠ .symbol head :: rest) :
    relationRows program "petta-unheaded-expression"
      [.apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none]] =
      [[.apply "ground-atom-expression-v1" [.collection .vec
        (OSLFCore.Bridge.GroundData.encodeList items) none]]] := by
  simp only [relationRows, results, atom?, decode_expression_raw]
  cases items with
  | nil => rfl
  | cons first rest =>
    cases first with
    | symbol head => exact False.elim (unheaded head rest rfl)
    | var name => rfl
    | expression fields => rfl
    | grounded value => rfl


@[local simp] private theorem variable_encoded_raw (name : String) :
    OSLFCore.Bridge.GroundData.encode (.var name) = .apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] := by
  exact variable_encoded name

@[local simp] private theorem integer_encoded_raw (value : Int) :
    OSLFCore.Bridge.GroundData.encode (.grounded (.int value)) = .apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]] := by
  exact integer_encoded value

@[local simp] private theorem string_encoded_raw (value : String) :
    OSLFCore.Bridge.GroundData.encode (.grounded (.string value)) = .apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]] := by
  exact string_encoded value

@[local simp] private theorem false_encoded_raw  :
    OSLFCore.Bridge.GroundData.encode (.grounded (.bool false)) = .apply "ground-atom-boolean-false-v1" [] := by
  exact false_encoded

@[local simp] private theorem true_encoded_raw  :
    OSLFCore.Bridge.GroundData.encode (.grounded (.bool true)) = .apply "ground-atom-boolean-true-v1" [] := by
  exact true_encoded

@[local simp] private theorem custom_encoded_raw (typeName data : String) :
    OSLFCore.Bridge.GroundData.encode (.grounded (.custom typeName data)) = .apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]] := by
  exact custom_encoded typeName data

@[local simp] private theorem unheaded_nil_grounded_rows
    (program : SpaceSemantics.Program)  :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec [] none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program ([])

@[local simp] private theorem unheaded_nil_unheaded_expression_rows
    (program : SpaceSemantics.Program)  :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec [] none]] = [[.apply "ground-atom-expression-v1" [.collection .vec [] none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program ([]) (by simp)

@[local simp] private theorem unheaded_var_grounded_rows
    (program : SpaceSemantics.Program) (name : String) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.var name :: rest)

@[local simp] private theorem unheaded_var_unheaded_expression_rows
    (program : SpaceSemantics.Program) (name : String) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-variable-v1" [.apply "source-sexpr-atom-v1" [.apply name []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.var name :: rest) (by simp)

@[local simp] private theorem unheaded_expression_grounded_rows
    (program : SpaceSemantics.Program) (fields : List Atom) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList fields) none] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.expression fields :: rest)

@[local simp] private theorem unheaded_expression_unheaded_expression_rows
    (program : SpaceSemantics.Program) (fields : List Atom) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList fields) none] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-expression-v1" [.collection .vec (OSLFCore.Bridge.GroundData.encodeList fields) none] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.expression fields :: rest) (by simp)

@[local simp] private theorem unheaded_integer_grounded_rows
    (program : SpaceSemantics.Program) (value : Int) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.grounded (.int value) :: rest)

@[local simp] private theorem unheaded_integer_unheaded_expression_rows
    (program : SpaceSemantics.Program) (value : Int) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-integer-v1" [.apply "source-sexpr-atom-v1" [.apply (Int.repr value) []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.grounded (.int value) :: rest) (by simp)

@[local simp] private theorem unheaded_string_grounded_rows
    (program : SpaceSemantics.Program) (value : String) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.grounded (.string value) :: rest)

@[local simp] private theorem unheaded_string_unheaded_expression_rows
    (program : SpaceSemantics.Program) (value : String) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-string-v1" [.apply "source-sexpr-atom-v1" [.apply value []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.grounded (.string value) :: rest) (by simp)

@[local simp] private theorem unheaded_false_grounded_rows
    (program : SpaceSemantics.Program) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-boolean-false-v1" [] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.grounded (.bool false) :: rest)

@[local simp] private theorem unheaded_false_unheaded_expression_rows
    (program : SpaceSemantics.Program) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-boolean-false-v1" [] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-boolean-false-v1" [] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.grounded (.bool false) :: rest) (by simp)

@[local simp] private theorem unheaded_true_grounded_rows
    (program : SpaceSemantics.Program) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-boolean-true-v1" [] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.grounded (.bool true) :: rest)

@[local simp] private theorem unheaded_true_unheaded_expression_rows
    (program : SpaceSemantics.Program) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-boolean-true-v1" [] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-boolean-true-v1" [] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.grounded (.bool true) :: rest) (by simp)

@[local simp] private theorem unheaded_custom_grounded_rows
    (program : SpaceSemantics.Program) (typeName data : String) (rest : List Atom) :
    relationRows program "petta-grounded" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    expression_grounded_rows_raw program (.grounded (.custom typeName data) :: rest)

@[local simp] private theorem unheaded_custom_unheaded_expression_rows
    (program : SpaceSemantics.Program) (typeName data : String) (rest : List Atom) :
    relationRows program "petta-unheaded-expression" [.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]] = [[.apply "ground-atom-expression-v1" [.collection .vec (.apply "ground-atom-custom-v1" [.apply "source-sexpr-atom-v1" [.apply typeName []], .apply "source-sexpr-atom-v1" [.apply data []]] :: OSLFCore.Bridge.GroundData.encodeList rest) none]]] := by
  simpa only [OSLFCore.Bridge.GroundData.encodeList, variable_encoded_raw, expression_encoded_raw,
    integer_encoded_raw, string_encoded_raw, false_encoded_raw, true_encoded_raw, custom_encoded_raw] using
    unheaded_rows_raw program (.grounded (.custom typeName data) :: rest) (by simp)

attribute [local simp] variable_encoded integer_encoded string_encoded false_encoded true_encoded
  custom_encoded OSLFCore.Bridge.GroundData.encodeList

set_option maxHeartbeats 2000000 in
theorem unheaded_frontier (program : SpaceSemantics.Program)
    (state bindings frames input output : Pattern) (items : List Atom)
    (unheaded : ∀ head rest, items ≠ .symbol head :: rest) :
    rewriteStepWithPremisesUsing (relationEnv program) language
      (configurationPattern state
        (evaluatePattern bindings (encoded (.expression items))) frames input output) =
      [configurationPattern state
        (argumentsPattern bindings (symbolPattern "petta-target-data-v1")
          (encodedList items) (expressionPattern []) (encoded (index 0))) frames input output] := by
  cases items with
  | nil =>
    simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, matchRelationArgs, encoded, encodedList_fields]
  | cons first rest =>
    cases first with
    | symbol head => exact False.elim (unheaded head rest rfl)
    | grounded value =>
      cases value <;> (try cases ‹Bool›) <;>
        simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, matchRelationArgs, encoded, encodedList_fields]
    | var name | expression fields =>
      simp +decide (config := {maxSteps := 300000}) [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      applyRuleBindings, applyBindings, matchPattern, matchArgs, mergeBindings,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, matchRelationArgs, encoded, encodedList_fields]

end InertControls

theorem fault_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String) (reason : Effects.Fault)
    (control : source.control = .fault reason) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, fault_encoded, fault_inert]
  simp [Eval.step, control]

theorem sequence_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String) (pending : List Eval.Control)
    (answers : List Atom) (control : source.control = .sequence pending answers) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, sequence_encoded]
  cases pending with
  | nil =>
      simp only [encodedControls, controlsData, encodedList_fields,
        OSLFCore.Bridge.GroundData.encodeList]
      rw [sequence_done_frontier]
      simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
        configuration_fields, returned_encoded, encodedList_fields]
  | cons first rest =>
      rw [pending_encoded_cons, sequence_enter_frontier]
      simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
        configuration_fields]
      rw [atom_list_encoded_cons, frame_encoded]
      simp only [encodedControls, encodedList_fields]

theorem construct_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (values : List Atom) (position : Nat)
    (control : source.control = .arguments bindings .data [] values position) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, arguments_encoded]
  have data : encoded (targetData .data) = symbolPattern "petta-target-data-v1" := by
    simp only [targetData, encoded, symbolPattern]
  rw [data]
  simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]
  rw [construct_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, returned_encoded, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList]
  simp only [OSLFCore.Bridge.GroundData.encode, expressionPattern]

theorem pending_argument_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (target : Eval.Target)
    (first : Atom) (rest values : List Atom) (position : Nat)
    (control : source.control = .arguments bindings target (first :: rest) values position) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun after => encode after names) := by
  rw [configuration_fields, control, arguments_encoded, pending_argument_frontier]
  cases target with
  | data =>
      simp only [Bool.false_eq_true, ↓reduceIte, Eval.step, control, Option.toList_some,
        List.map_cons, List.map_nil, configuration_fields, evaluate_encoded]
      rw [atom_list_encoded_cons, frame_encoded]
  | function head =>
      cases demand : Eval.argumentIsRaw program head position with
      | false =>
          simp only [Eval.step, control, demand, Bool.false_eq_true, ↓reduceIte,
            Option.toList_some, List.map_cons, List.map_nil, configuration_fields,
            evaluate_encoded]
          rw [atom_list_encoded_cons, frame_encoded]
      | true =>
          simp only [Eval.step, control, demand, ↓reduceIte,
            Option.toList_some, List.map_cons, List.map_nil, configuration_fields,
            returned_encoded]
          rw [atom_list_encoded_cons, atom_list_encoded_cons, frame_encoded]
          simp only [OSLFCore.Bridge.GroundData.encodeList]

private theorem io_arguments_shape (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (head : String) (values : List Atom) (position : Nat) :
    encoded (controlData (.arguments bindings (.function head) [] values position)) =
      argumentsPattern (encoded (bindingsData bindings)) (functionPattern (stringPattern head))
        (expressionPattern []) (encodedList values) (encoded (index position)) := by
  rw [arguments_encoded, target_encoded]
  simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]

private theorem io_fault_shape (head : String) :
    encoded (controlData (.fault (.invalidArguments head))) =
      faultPattern (taggedPattern "petta-fault-arguments-v1" [stringPattern head]) := by
  simp only [controlData, faultData, encoded, faultPattern, taggedPattern, expressionPattern,
    symbolPattern, stringPattern, text, OSLFCore.Bridge.GroundData.encode,
    OSLFCore.Bridge.GroundData.encodeList]

theorem read_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (values : List Atom)
    (position : Nat)
    (control : source.control = .arguments bindings (.function "readln!") [] values position) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun after => encode after names) := by
  rw [configuration_fields, control, io_arguments_shape]
  cases values with
  | nil =>
      rw [encodedList_fields ([] : List Atom)]
      simp only [OSLFCore.Bridge.GroundData.encodeList]
      cases input : source.input with
      | nil =>
          simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]
          rw [read_end_frontier]
          simp [Eval.step, control, input, Eval.ioHead, configuration_fields,
            returned_encoded, encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]
          rfl
      | cons first rest =>
          rw [read_line_frontier program (encoded (stateData source.state names))
            (encoded (bindingsData bindings)) (encoded (index position))
            (encodedList (source.frames.map frameData)) (encodedList source.output) first rest]
          simp [Eval.step, control, input, Eval.ioHead, configuration_fields,
            returned_encoded, encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]
          rfl
  | cons first rest =>
      rw [read_bad_cons_frontier program (encoded (stateData source.state names))
        (encoded (bindingsData bindings)) (encoded (index position))
        (encodedList (source.frames.map frameData)) (encodedList source.input)
        (encodedList source.output) first rest]
      simp [Eval.step, control, Eval.ioHead, configuration_fields, io_fault_shape]

theorem print_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (values : List Atom)
    (position : Nat)
    (control : source.control = .arguments bindings (.function "println!") [] values position) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun after => encode after names) := by
  rw [configuration_fields, control, io_arguments_shape]
  cases values with
  | nil =>
      rw [print_bad_nil_frontier]
      simp [Eval.step, control, configuration_fields, io_fault_shape, Eval.ioHead]
  | cons first rest =>
      cases rest with
      | nil =>
          rw [atom_list_encoded_cons]
          simp only [OSLFCore.Bridge.GroundData.encodeList]
          rw [print_frontier program (encoded (stateData source.state names))
            (encoded (bindingsData bindings)) (encoded (index position))
            (encodedList (source.frames.map frameData)) (encodedList source.input)
            first source.output]
          simp [Eval.step, control, configuration_fields, returned_encoded,
            encodedList_fields, OSLFCore.Bridge.GroundData.encodeList, Eval.ioHead]
          rfl
      | cons second rest =>
          rw [print_bad_many_frontier]
          simp [Eval.step, control, configuration_fields, io_fault_shape, Eval.ioHead]


theorem eval_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (values : List Atom)
    (position : Nat)
    (control : source.control = .arguments bindings (.function "eval") [] values position) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun after => encode after names) := by
  rw [configuration_fields, control, io_arguments_shape]
  cases values with
  | nil =>
      rw [eval_bad_nil_frontier]
      simp [Eval.step, control, configuration_fields, io_fault_shape, Eval.ioHead]
  | cons first rest =>
      cases rest with
      | nil =>
          rw [atom_list_encoded_cons]
          simp only [OSLFCore.Bridge.GroundData.encodeList]
          rw [evaluate_code_frontier program (encoded (stateData source.state names))
            (encoded (bindingsData bindings)) (encoded (index position))
            (encodedList (source.frames.map frameData)) (encodedList source.input)
            (encodedList source.output) first]
          simp [Eval.step, control, configuration_fields, evaluate_encoded,
            bindingsData, Eval.ioHead]
          rw [show encoded (.expression []) = expressionPattern [] by
            simp only [encoded, OSLFCore.Bridge.GroundData.encode,
              OSLFCore.Bridge.GroundData.encodeList, expressionPattern]]
      | cons second rest =>
          rw [eval_bad_many_frontier]
          simp [Eval.step, control, configuration_fields, io_fault_shape, Eval.ioHead]

/-- Every I/O head has its exact successor, including invalid argument counts. -/
theorem io_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String)
    (values : List Atom) (position : Nat)
    (control : source.control = .arguments bindings (.function head) [] values position)
    (isIO : Eval.ioHead head = true) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun after => encode after names) := by
  have heads : head = "readln!" ∨ head = "println!" ∨ head = "eval" := by
    simpa [Eval.ioHead] using isIO
  rcases heads with rfl | rfl | rfl
  · exact read_frontier_eq_step program source names bindings values position control
  · exact print_frontier_eq_step program source names bindings values position control
  · exact eval_frontier_eq_step program source names bindings values position control


theorem primitive_success_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String)
    (values answers : List Atom) (position : Nat) (after : Effects.State)
    (control : source.control = .arguments bindings (.function head) [] values position)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (notIO : Eval.ioHead head = false) (native : StdLib.known head = true)
    (returned : StdLib.apply source.state head values = .ok (after, answers)) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map
        (fun target => encode target (cellSupportAfter source names)) := by
  rw [configuration_fields, control, arguments_encoded, target_encoded]
  rw [encodedList_fields ([] : List Atom)]
  simp only [OSLFCore.Bridge.GroundData.encodeList]
  rw [primitive_success_frontier program source.state after
    (encoded (bindingsData bindings)) (encoded (index position))
    (encodedList (source.frames.map frameData)) (encodedList source.input)
    (encodedList source.output) head values answers names vacant covers notIO native returned]
  simp only [Eval.step, control, notIO, native, returned, Bool.false_eq_true,
    ↓reduceIte, Option.toList_some, List.map_cons, List.map_nil, configuration_fields,
    returned_encoded, cellSupportAfter]

theorem primitive_fault_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String)
    (values : List Atom) (position : Nat) (reason : Effects.Fault)
    (control : source.control = .arguments bindings (.function head) [] values position)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (notIO : Eval.ioHead head = false) (native : StdLib.known head = true)
    (failed : StdLib.apply source.state head values = .error reason) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map
        (fun target => encode target (cellSupportAfter source names)) := by
  rw [configuration_fields, control, arguments_encoded, target_encoded]
  rw [encodedList_fields ([] : List Atom)]
  simp only [OSLFCore.Bridge.GroundData.encodeList]
  rw [primitive_fault_frontier program source.state
    (encoded (bindingsData bindings)) (encoded (index position))
    (encodedList (source.frames.map frameData)) (encodedList source.input)
    (encodedList source.output) head values reason names vacant covers notIO native failed]
  simp only [Eval.step, control, notIO, native, failed, Bool.false_eq_true,
    ↓reduceIte, Option.toList_some, List.map_cons, List.map_nil, configuration_fields,
    fault_encoded, cellSupportAfter, failed_primitive_support names failed]

theorem equations_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String)
    (values : List Atom) (position : Nat)
    (control : source.control = .arguments bindings (.function head) [] values position)
    (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map
        (fun target => encode target (cellSupportAfter source names)) := by
  have notWriter : head ≠ "change-state!" := by
    intro same
    subst head
    simp [StdLib.known] at notNative
  rw [configuration_fields, control, arguments_encoded, target_encoded]
  rw [encodedList_fields ([] : List Atom)]
  simp only [OSLFCore.Bridge.GroundData.encodeList]
  rw [equations_frontier program (encoded (stateData source.state names))
    (encoded (bindingsData bindings)) (encoded (index position))
    (encodedList (source.frames.map frameData)) (encodedList source.input)
    (encodedList source.output) head values notIO notNative]
  simp only [Eval.step, control, notIO, notNative, Bool.false_eq_true,
    ↓reduceIte, Option.toList_some, List.map_cons, List.map_nil, configuration_fields,
    sequence_encoded, cellSupportAfter,
    primitiveCellSupport_of_not_writer head values names notWriter]
  simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]

/-- All completed function calls have their exact machine frontier, including
I/O, primitive failure and ordered equation dispatch. Cell names are updated
only by the actual successful cell-writing call. -/
theorem finished_function_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String)
    (values : List Atom) (position : Nat)
    (control : source.control = .arguments bindings (.function head) [] values position)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map
        (fun target => encode target (cellSupportAfter source names)) := by
  cases isIO : Eval.ioHead head with
  | true =>
      have notWriter : head ≠ "change-state!" := by
        intro same
        subst head
        simp [Eval.ioHead] at isIO
      rw [io_frontier_eq_step program source names bindings head values position control isIO]
      simp only [cellSupportAfter, control,
        primitiveCellSupport_of_not_writer head values names notWriter]
  | false =>
      cases native : StdLib.known head with
      | false =>
          exact equations_frontier_eq_step program source names bindings head
            values position control isIO native
      | true =>
          cases applied : StdLib.apply source.state head values with
          | error reason =>
              exact primitive_fault_frontier_eq_step program source names
                bindings head values position reason control vacant covers isIO native applied
          | ok result =>
              rcases result with ⟨after, answers⟩
              exact primitive_success_frontier_eq_step program source names bindings head
                values answers position after control vacant covers isIO native applied

/-- Every returned-answer continuation has exactly its machine successor;
the empty continuation has none. This covers all existing frame constructors. -/
theorem returned_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String) (answers : List Atom)
    (control : source.control = .returned answers) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, returned_encoded]
  cases frames : source.frames with
  | nil =>
      simp only [List.map_nil, encodedList_fields,
        OSLFCore.Bridge.GroundData.encodeList]
      rw [terminal_inert]
      simp [Eval.step, control, frames]
  | cons first rest =>
      rw [frames_encoded_cons, frame_encoded]
      cases first with
      | collect =>
          rw [collapse_return_frontier]
          simp only [Eval.step, control, frames, Option.toList_some, List.map_cons, List.map_nil,
            configuration_fields, returned_encoded, encodedList_fields,
            OSLFCore.Bridge.GroundData.encodeList]
          simp only [OSLFCore.Bridge.GroundData.encode, expressionPattern]
      | sequence pending collected =>
          rw [sequence_return_frontier]
          simp only [Eval.step, control, frames, Option.toList_some, List.map_cons, List.map_nil,
            configuration_fields, sequence_encoded, encodedList_fields]
      | argument bindings target pending values position =>
          rw [argument_return_frontier]
          simp only [Eval.step, control, frames, Option.toList_some, List.map_cons, List.map_nil,
            configuration_fields, sequence_encoded, encodedList_fields,
            OSLFCore.Bridge.GroundData.encodeList]
      | bind bindings pattern body =>
          rw [binding_return_frontier]
          simp only [Eval.step, control, frames, Option.toList_some, List.map_cons, List.map_nil,
            configuration_fields, sequence_encoded, encodedList_fields,
            OSLFCore.Bridge.GroundData.encodeList]
      | select bindings cases =>
          rw [case_return_frontier]
          simp only [Eval.step, control, frames, Option.toList_some, List.map_cons, List.map_nil,
            configuration_fields, sequence_encoded, encodedList_fields,
            OSLFCore.Bridge.GroundData.encodeList]
      | branch bindings yes no =>
          rw [if_return_frontier]
          simp only [Eval.step, control, frames, Option.toList_some, List.map_cons, List.map_nil,
            configuration_fields, sequence_encoded, encodedList_fields,
            OSLFCore.Bridge.GroundData.encodeList]

/-- Preservation and no invention for all returned-answer continuations in the
actual generated GSLT, through the existing operational judgment. -/
theorem returned_generated_step_iff (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String) (answers : List Atom)
    (control : source.control = .returned answers) (target : Pattern) :
    (langGSLTUsing (relationEnv program) language).Step (encode source names) target ↔
      ∃ after, DeclarativeSpec.Transition program source after ∧ target = encode after names := by
  rw [← frontier_iff_generated_step, returned_frontier_eq_step program source names answers control]
  simp only [List.mem_map, Option.mem_toList, Eval.step_iff_transition]
  constructor
  · rintro ⟨after, transition, rfl⟩
    exact ⟨after, transition, rfl⟩
  · rintro ⟨after, transition, rfl⟩
    exact ⟨after, transition, rfl⟩

theorem variable_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String)
    (control : source.control = .evaluate bindings (.var name)) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, variable_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, returned_encoded, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList]
  rfl


theorem grounded_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (value : OSLFCore.GroundedValue)
    (control : source.control = .evaluate bindings (.grounded value)) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, grounded_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, returned_encoded, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList]
  rfl


theorem let_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (pattern value body : Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "let", pattern, value, body])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, let_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, evaluate_encoded]
  rw [atom_list_encoded_cons, frame_encoded]

theorem if_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (condition yes no : Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "if", condition, yes, no])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, if_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, evaluate_encoded]
  rw [atom_list_encoded_cons, frame_encoded]

theorem collapse_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (expression : Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "collapse", expression])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, collapse_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, evaluate_encoded]
  rw [atom_list_encoded_cons, frame_encoded]

theorem empty_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) 
    (control : source.control = .evaluate bindings (.expression [.symbol "empty"])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, empty_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, returned_encoded]
  simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]

theorem quote_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (expression : Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "quote", expression])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, quote_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, returned_encoded]
  simp only [encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]
  rfl

theorem let_star_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (pairs : List Atom) (body : Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "let*", .expression pairs, body])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, let_star_frontier]
  cases built : Eval.nestedLets pairs body
  all_goals simp only [Eval.step, control, built, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, evaluate_encoded, fault_encoded]
  · rw [← fault_encoded, io_fault_shape]
    rfl

theorem case_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (value : Atom) (rows : List Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "case", value, .expression rows])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, case_frontier]
  cases parsed : Eval.readCases rows
  all_goals simp only [Eval.step, control, parsed, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, evaluate_encoded, fault_encoded]
  · rw [← fault_encoded, io_fault_shape]
    rfl
  · rw [atom_list_encoded_cons, frame_encoded]

theorem superpose_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (alternatives : List Atom)
    (control : source.control = .evaluate bindings (.expression [.symbol "superpose", .expression alternatives])) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, superpose_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, sequence_encoded, encodedList_fields,
    OSLFCore.Bridge.GroundData.encodeList]

theorem symbol_generated_step_iff (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String)
    (control : source.control = .evaluate bindings (.symbol name)) (target : Pattern) :
    (langGSLTUsing (relationEnv program) language).Step (encode source names) target ↔
      target = encode {source with control := .returned [.symbol name]} names := by
  rw [← frontier_iff_generated_step, configuration_fields, control, evaluate_encoded]
  change target ∈ rewriteStepWithPremisesUsing (relationEnv program) language
    (configurationPattern _ (evaluatePattern _ (symbolPattern name)) _ _ _) ↔ _
  rw [symbol_frontier]
  simp only [List.mem_singleton, configuration_fields, returned_encoded]
  simp only [encodedList, encoded, expressionPattern, symbolPattern,
    OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList]

theorem symbol_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String)
    (control : source.control = .evaluate bindings (.symbol head)) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded]
  change rewriteStepWithPremisesUsing (relationEnv program) language
    (configurationPattern _ (evaluatePattern _ (symbolPattern head)) _ _ _) = _
  rw [symbol_frontier]
  simp only [Eval.step, control, Option.toList_some, List.map_cons, List.map_nil,
    configuration_fields, returned_encoded, encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]
  rfl

theorem ordinary_headed_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String) (arguments : List Atom)
    (control : source.control = .evaluate bindings (.expression (.symbol head :: arguments)))
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, ordinary_headed_frontier _ _ _ _ _ _ _ _ ordinary]
  cases callable : Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)
  · rw [Eval.transition_step (DeclarativeSpec.Transition.data_enter control ordinary callable)]
    simp only [Bool.false_eq_true, ↓reduceIte, Option.toList_some, List.map_cons, List.map_nil,
      configuration_fields, arguments_encoded, target_encoded, encodedList_fields,
      OSLFCore.Bridge.GroundData.encodeList]
    simp only [encoded, OSLFCore.Bridge.GroundData.encode, OSLFCore.Bridge.GroundData.encodeList, expressionPattern]
  · rw [Eval.transition_step (DeclarativeSpec.Transition.call_enter control ordinary callable)]
    simp only [↓reduceIte, Option.toList_some, List.map_cons, List.map_nil,
      configuration_fields, arguments_encoded, target_encoded, encodedList_fields,
      OSLFCore.Bridge.GroundData.encodeList]

theorem unheaded_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (items : List Atom)
    (control : source.control = .evaluate bindings (.expression items))
    (unheaded : ∀ head rest, items ≠ .symbol head :: rest) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map (fun target => encode target names) := by
  rw [configuration_fields, control, evaluate_encoded, unheaded_frontier _ _ _ _ _ _ _ unheaded]
  rw [Eval.transition_step (DeclarativeSpec.Transition.expression_enter control unheaded)]
  simp only [Option.toList_some, List.map_cons, List.map_nil, configuration_fields,
    arguments_encoded, target_encoded, encodedList_fields, OSLFCore.Bridge.GroundData.encodeList]

set_option maxHeartbeats 1000000 in
/-- The full authored frontier for every actual nonterminal machine step. -/
theorem some_frontier_eq_step (program : SpaceSemantics.Program)
    (source after : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (computed : Eval.step program source = some after) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map
        (fun target => encode target (cellSupportAfter source names)) := by
  have transition := Eval.step_transition computed
  cases transition
  all_goals first
    | exact finished_function_frontier_eq_step program source names _ _ _ _ (by assumption) vacant covers
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        sequence_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        construct_frontier_eq_step program source names _ _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        pending_argument_frontier_eq_step program source names _ _ _ _ _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        returned_frontier_eq_step program source names _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        variable_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        symbol_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        grounded_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        let_frontier_eq_step program source names _ _ _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        let_star_frontier_eq_step program source names _ _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        case_frontier_eq_step program source names _ _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        if_frontier_eq_step program source names _ _ _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        collapse_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        superpose_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        empty_frontier_eq_step program source names _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        quote_frontier_eq_step program source names _ _ (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        ordinary_headed_frontier_eq_step program source names _ _ _ (by assumption) (by assumption)
    | simpa only [cellSupportAfter, (by assumption : source.control = _)] using
        unheaded_frontier_eq_step program source names _ _ (by assumption) (by assumption)
set_option maxHeartbeats 1000000 in
theorem no_step_terminal (program : SpaceSemantics.Program) (source : Eval.Configuration)
    (computed : Eval.step program source = none) :
    (∃ reason, source.control = .fault reason) ∨
      ∃ answers, source.control = .returned answers ∧ source.frames = [] := by
  cases control : source.control with
  | fault reason => exact Or.inl ⟨reason, rfl⟩
  | returned answers =>
    cases frames : source.frames with
    | nil => exact Or.inr ⟨answers, rfl, rfl⟩
    | cons frame rest =>
      cases frame <;> simp [Eval.step, control, frames] at computed
  | sequence pending answers =>
    cases pending <;> simp [Eval.step, control] at computed
  | arguments bindings target pending values position =>
    simp only [Eval.step, control] at computed
    repeat' split at computed
    all_goals simp_all
  | evaluate bindings expression =>
    simp only [Eval.step, control] at computed
    repeat' split at computed
    all_goals simp_all


theorem none_frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (computed : Eval.step program source = none) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) = [] := by
  rcases no_step_terminal program source computed with ⟨reason, control⟩ | ⟨answers, control, _⟩
  · rw [fault_frontier_eq_step program source names reason control, computed]
    rfl
  · rw [returned_frontier_eq_step program source names answers control, computed]
    rfl

/-- All and only the actual successor configurations occur in the authored frontier. -/
theorem frontier_eq_step (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) :
    rewriteStepWithPremisesUsing (relationEnv program) language (encode source names) =
      (Eval.step program source).toList.map
        (fun target => encode target (cellSupportAfter source names)) := by
  cases computed : Eval.step program source with
  | none =>
    simpa only [computed, Option.toList_none, List.map_nil] using
      none_frontier_eq_step program source names computed
  | some target =>
    simpa only [computed] using some_frontier_eq_step program source target names vacant covers computed

/-- Exact one-step correspondence with the generated LanguageDef GSLT. -/
theorem generated_step_iff (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) (target : Pattern) :
    (langGSLTUsing (relationEnv program) language).Step (encode source names) target ↔
      ∃ after, DeclarativeSpec.Transition program source after ∧
        target = encode after (cellSupportAfter source names) := by
  rw [← frontier_iff_generated_step, frontier_eq_step program source names vacant covers]
  simp only [List.mem_map, Option.mem_toList, Eval.step_iff_transition]
  constructor
  · rintro ⟨after, transition, rfl⟩
    exact ⟨after, transition, rfl⟩
  · rintro ⟨after, transition, rfl⟩
    exact ⟨after, transition, rfl⟩

/-- A configuration path is represented by actual generated language steps. -/
theorem path_realized (program : SpaceSemantics.Program)
    (source target : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (path : (Eval.theory program).MultiStep source target) :
    ∃ finalNames,
      (langGSLTUsing (relationEnv program) language).MultiStep
        (encode source names) (encode target finalNames) ∧
      NamedSpaces.Store.EmptyTail target.state [] ∧
      (∀ name, name ∉ finalNames → target.state.cells name = none) := by
  let property (first last : (Eval.theory program).Term) :=
    ∀ (names : List String), NamedSpaces.Store.EmptyTail first.state [] →
      (∀ name, name ∉ names → first.state.cells name = none) →
      ∃ finalNames,
        (langGSLTUsing (relationEnv program) language).MultiStep
          (encode first names) (encode last finalNames) ∧
        NamedSpaces.Store.EmptyTail last.state [] ∧
        (∀ name, name ∉ finalNames → last.state.cells name = none)
  have realized : property source target := by
    refine Mettapedia.GSLT.GSLT.MultiStep.rec (S := Eval.theory program)
      (motive := fun first last _ => property first last) ?_ ?_ path
    · intro initial names vacant covers
      exact ⟨names, .refl _, vacant, covers⟩
    · intro first middle last transition _ ih names vacant covers
      have actual : DeclarativeSpec.Transition program first middle := transition
      have middleVacant := DeclarativeSpec.transition_empty_tail vacant actual
      have middleCovers := transition_support names covers actual
      obtain ⟨finalNames, generated, targetVacant, targetCovers⟩ :=
        ih (cellSupportAfter first names) middleVacant middleCovers
      have firstStep := (generated_step_iff program first names vacant covers _).mpr ⟨middle, actual, rfl⟩
      exact ⟨finalNames, .step firstStep generated, targetVacant, targetCovers⟩
  exact realized names vacant covers

private theorem reflect_path_from (program : SpaceSemantics.Program) (start target : Pattern)
    (path : (langGSLTUsing (relationEnv program) language).MultiStep start target) :
    ∀ (source : Eval.Configuration) (names : List String), start = encode source names →
      NamedSpaces.Store.EmptyTail source.state [] →
      (∀ name, name ∉ names → source.state.cells name = none) →
      ∃ (after : Eval.Configuration) (afterNames : List String),
        (Eval.theory program).MultiStep source after ∧ target = encode after afterNames ∧
        NamedSpaces.Store.EmptyTail after.state [] ∧
        (∀ name, name ∉ afterNames → after.state.cells name = none) := by
  refine Mettapedia.GSLT.GSLT.MultiStep.rec
    (S := langGSLTUsing (relationEnv program) language)
    (motive := fun first last _ =>
      ∀ (source : Eval.Configuration) (names : List String), first = encode source names →
        NamedSpaces.Store.EmptyTail source.state [] →
        (∀ name, name ∉ names → source.state.cells name = none) →
        ∃ (after : Eval.Configuration) (afterNames : List String),
          (Eval.theory program).MultiStep source after ∧ last = encode after afterNames ∧
          NamedSpaces.Store.EmptyTail after.state [] ∧
          (∀ name, name ∉ afterNames → after.state.cells name = none))
    ?_ ?_ path
  · intro initial source names same vacant covers
    exact ⟨source, names, .refl _, same, vacant, covers⟩
  · intro first middle last firstStep _ ih source names same vacant covers
    rw [same] at firstStep
    obtain ⟨intermediate, actual, middleSame⟩ :=
      (generated_step_iff program source names vacant covers middle).mp firstStep
    obtain ⟨after, afterNames, actualPath, terminalSame, terminalVacant, terminalCovers⟩ :=
      ih intermediate (cellSupportAfter source names) middleSame
        (DeclarativeSpec.transition_empty_tail vacant actual) (transition_support names covers actual)
    exact ⟨after, afterNames, .step actual actualPath, terminalSame, terminalVacant, terminalCovers⟩

/-- Every generated path from a represented state decodes to the source judgment. -/
theorem generated_path_reflected (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) (target : Pattern)
    (path : (langGSLTUsing (relationEnv program) language).MultiStep (encode source names) target) :
    ∃ (after : Eval.Configuration) (afterNames : List String),
      (Eval.theory program).MultiStep source after ∧ target = encode after afterNames ∧
      NamedSpaces.Store.EmptyTail after.state [] ∧
      (∀ name, name ∉ afterNames → after.state.cells name = none) :=
  reflect_path_from program _ _ path source names rfl vacant covers

/-- Whole completed observations, including store and I/O, agree with the language graph. -/
theorem completed_derivation_iff_generated_path (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (state : Effects.State) (answers remaining printed : List Atom) :
    DeclarativeSpec.Runs program source (.complete state answers remaining printed) ↔
      ∃ target,
        (langGSLTUsing (relationEnv program) language).MultiStep (encode source names) target ∧
        decode target = some (Eval.finished state answers remaining printed) := by
  constructor
  · intro running
    have path := (Eval.completed_derivation_iff_path program source state answers remaining printed).mp running
    obtain ⟨finalNames, generated, terminalVacant, terminalCovers⟩ :=
      path_realized program source _ names vacant covers path
    exact ⟨_, generated, decode_encode _ finalNames terminalVacant terminalCovers⟩
  · rintro ⟨target, generated, decoded⟩
    obtain ⟨after, afterNames, path, same, terminalVacant, terminalCovers⟩ :=
      generated_path_reflected program source names vacant covers target generated
    have reconstructed := decode_encode after afterNames terminalVacant terminalCovers
    rw [same] at decoded
    have terminal : after = Eval.finished state answers remaining printed :=
      Option.some.inj (reconstructed.symm.trans decoded)
    rw [terminal] at path
    exact (Eval.completed_derivation_iff_path program source state answers remaining printed).mpr path

/-- The existing executable and the authored language have the same completed observations. -/
theorem completed_run_iff_generated_path (program : SpaceSemantics.Program)
    (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (state : Effects.State) (answers remaining printed : List Atom) :
    (∃ fuel, Eval.run program fuel source = .complete state answers remaining printed) ↔
      ∃ target,
        (langGSLTUsing (relationEnv program) language).MultiStep (encode source names) target ∧
        decode target = some (Eval.finished state answers remaining printed) :=
  (Eval.completed_run_iff_derivation program source state answers remaining printed).trans
    (completed_derivation_iff_generated_path program source names vacant covers state answers remaining printed)

end Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef
