import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax
import Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution
import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution

/-!
# Authored controller clauses and their actual generated bodies

The selected syntax fold consumes the original ordered Run/Closure premises
and explicit selected modes. It reproduces the corresponding equations in the
whole eight-source candidate, including functional-callee `once` and relational
literal wrappers. Mode inference and native emission correctness are separate
obligations. Execution below uses the existing finite ground target model and
actual equation inventory, not a supplied controller-answer function.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedControllerSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult bindAnswers)
open GeneratedPeTTaTemplateInstantiation
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open PlainBnfGeneratedScalarOrderSyntax (program selectedRows equationsFor_program literal_heads)
open PlainBnfGeneratedPeTTaSyntax (sourceTerm? sourceTerms? modeBits quote letTerm resultTag)

/-- The finite mode selection observed in this emitted family. This is an
input to the selected rendering branch, not a proof of mode inference. -/
def selectedMode? (relation : String) : Option (Nat × Nat × Bool) := do
  let functional ← match relation with
    | "BNFDiscoveryRunV1" | "BNFDiscoveryClosureV1" | "BNFDiscoveryWakeV1" => some false
    | "BNFDiscoveryHeapCombineV1" | "BNFAppendNameV1" |
      "BNFGraphTrieLookupV1" | "BNFDiscoveryDependentsV1" => some true
    | _ => none
  let (inputs, outputs) ← PlainBnfRunSourceFamily.mode? relation
  return (inputs, outputs, functional)

def selectedName (relation : String) (inputs outputs : Nat) (functional : Bool) : String :=
  (if functional then "gslt:fn:" else "gslt:mode:") ++ relation ++ ":" ++ modeBits inputs outputs

def applicationParts? : SExpr → Option (Bool × SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs, functional) ← selectedMode? relation
      if arguments.length != inputs + outputs then none else do
        let arguments' ← sourceTerms? (arguments.take inputs)
        let results ← sourceTerms? (arguments.drop inputs)
        let tag := resultTag relation inputs outputs
        let result := if outputs = 0 then .atom tag else .list (.atom tag :: results)
        return (functional, .list (.atom (selectedName relation inputs outputs functional) :: arguments'), result)
  | _ => none

def rawWrapper (call : SExpr) : SExpr :=
  .list [.atom "superpose", .list [.atom "collapse", call]]

def selectedValue (callerFunctional calleeFunctional : Bool) (call : SExpr) : SExpr :=
  if !calleeFunctional then rawWrapper call
  else if !callerFunctional then .list [.atom "once", call]
  else call

def premises? (callerFunctional : Bool) : List SExpr → SExpr → Option SExpr
  | [], continuation => some continuation
  | premise :: tail, final => do
      let (functional, call, result) ← applicationParts? premise
      let continuation ← premises? callerFunctional tail final
      return letTerm result (selectedValue callerFunctional functional call) continuation

def clause? (source : Rewrite) : Option SExpr := do
  let (functional, head, result) ← applicationParts? source.head
  let body ← premises? functional source.body (quote result)
  return .list [.atom "=", head, body]

def runSymbol : String := "gslt:mode:BNFDiscoveryRunV1:111110"
def closureSymbol : String := "gslt:mode:BNFDiscoveryClosureV1:11110"
def runTag : String := "gslt:result:BNFDiscoveryRunV1:111110"
def closureTag : String := "gslt:result:BNFDiscoveryClosureV1:11110"
def wakeSymbol : String := "gslt:mode:BNFDiscoveryWakeV1:1111110"
def wakeTag : String := "gslt:result:BNFDiscoveryWakeV1:1111110"

def rows : List (Nat × SExpr) := selectedRows runSymbol ++ selectedRows closureSymbol

theorem rows_count : rows.length = 4 := rfl

def row (index : Fin 4) : Nat × SExpr := rows[index.val]'(by rw [rows_count]; exact index.isLt)

theorem source_to_actual_equations : PlainBnfRunSourceFamily.rows.mapM clause? =
    some (rows.map Prod.snd) := rfl

theorem occurrence_order : rows.map Prod.fst = [1970, 1974, 1979, 1989] := rfl

theorem duplicate_source_occurrences {source : Rewrite} {target : SExpr}
    (emitted : clause? source = some target) :
    [source, source].mapM clause? = some [target, target] := by simp [emitted]

theorem wrong_arity_refused : applicationParts?
    (.list [.atom "BNFDiscoveryRunV1", .atom "?mode"]) = none := rfl

theorem row_present (index : Fin 4) : (equation? (row index).2).isSome = true := by
  fin_cases index <;> rfl

def head (index : Fin 4) : SExpr := ((equation? (row index).2).get (row_present index)).1
def body (index : Fin 4) : SExpr := ((equation? (row index).2).get (row_present index)).2

theorem row_equation (index : Fin 4) : equation? (row index).2 = some (head index, body index) := by
  fin_cases index <;> rfl

theorem whole_run_rows : equationsFor runSymbol program = [row 0, row 1, row 2] := by
  rw [equationsFor_program]; rfl

theorem whole_closure_rows : equationsFor closureSymbol program = [row 3] := by
  rw [equationsFor_program]; rfl

def heapNil : SExpr := .atom "BNFDiscoveryHeapNilV1"
def heap (node children siblings : SExpr) : SExpr :=
  .list [.atom "BNFDiscoveryHeapV1", node, children, siblings]
def queues (current following scheduled : SExpr) : SExpr :=
  .list [.atom "BNFDiscoveryQueuesV1", current, following, scheduled]
def runCall (mode reverse lexicals known current following scheduled : SExpr) : SExpr :=
  .list [.atom runSymbol, mode, reverse, lexicals, known, queues current following scheduled]
def runResult (value : SExpr) : SExpr := .list [.atom runTag, value]

theorem done_head : head 0 = runCall (.atom "$mode") (.atom "$reverse") (.atom "$lexicals")
    (.atom "$known") heapNil heapNil (.atom "$scheduled") := rfl
theorem rollover_head : head 1 = runCall (.atom "$mode") (.atom "$reverse") (.atom "$lexicals")
    (.atom "$known") heapNil (heap (.atom "$node") (.atom "$children") (.atom "$siblings"))
    (.atom "$scheduled") := rfl
theorem publish_head : head 2 = runCall (.atom "$mode") (.atom "$reverse") (.atom "$lexicals")
    (.atom "$known")
    (heap (.list [.atom "BNFDiscoveryDefinitionV1", .atom "$rank", .atom "$name", .atom "$expression", .atom "$span"])
      (.atom "$children") heapNil) (.atom "$following") (.atom "$scheduled") := rfl

theorem done_body : body 0 = quote (runResult (.atom "$known")) := rfl
theorem rollover_body : body 1 = letTerm (runResult (.atom "$result"))
    (rawWrapper (runCall (.atom "$mode") (.atom "$reverse") (.atom "$lexicals") (.atom "$known")
      (heap (.atom "$node") (.atom "$children") (.atom "$siblings")) heapNil (.atom "$scheduled")))
    (quote (runResult (.atom "$result"))) := rfl

def dataHeads : List String :=
  ["BNFDiscoveryQueuesV1", "BNFDiscoveryHeapV1", "BNFDiscoveryKnownV1", runTag, wakeTag]

def doneBindings (mode reverse lexicals known scheduled : SExpr) : Bindings :=
  [("$reverse", encode reverse), ("$known", encode known), ("$scheduled", encode scheduled),
    ("$lexicals", encode lexicals), ("$mode", encode mode)]

def rolloverBindings (mode reverse lexicals known node children siblings scheduled : SExpr) : Bindings :=
  [("$reverse", encode reverse), ("$known", encode known), ("$scheduled", encode scheduled),
    ("$node", encode node), ("$siblings", encode siblings), ("$children", encode children),
    ("$lexicals", encode lexicals), ("$mode", encode mode)]

theorem dispatch_done (mode reverse lexicals known scheduled : SExpr) :
    dispatch [] (runCall mode reverse lexicals known heapNil heapNil scheduled) program =
      [(row 0, doneBindings mode reverse lexicals known scheduled)] := by
  rw [show runCall mode reverse lexicals known heapNil heapNil scheduled =
      .list (.atom runSymbol :: [mode, reverse, lexicals, known, queues heapNil heapNil scheduled]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, whole_run_rows]
  simp [dispatch, matchEquation, row_equation, done_head, rollover_head, publish_head,
    runCall, heapNil, heap, queues, runSymbol, bindResult, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, doneBindings]

theorem dispatch_rollover (mode reverse lexicals known node children siblings scheduled : SExpr) :
    dispatch [] (runCall mode reverse lexicals known heapNil (heap node children siblings) scheduled) program =
      [(row 1, rolloverBindings mode reverse lexicals known node children siblings scheduled)] := by
  rw [show runCall mode reverse lexicals known heapNil (heap node children siblings) scheduled =
      .list (.atom runSymbol :: [mode, reverse, lexicals, known, queues heapNil (heap node children siblings) scheduled]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, whole_run_rows]
  simp [dispatch, matchEquation, row_equation, done_head, rollover_head, publish_head,
    runCall, heapNil, heap, queues, runSymbol, bindResult, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, rolloverBindings]

theorem run_ordinary : reserved runSymbol = false := rfl
theorem run_known : knownFunction program runSymbol = true := by rw [knownFunction, whole_run_rows]; rfl
theorem run_arity : hasArity program runSymbol 5 = true := by
  rw [hasArity, whole_run_rows]
  simp [row_equation, done_head, runCall]

theorem run_done_body (depth : Nat) (mode reverse lexicals known scheduled : SExpr) :
    run depth program dataHeads (runCall mode reverse lexicals known heapNil heapNil scheduled) =
      eval depth program dataHeads (doneBindings mode reverse lexicals known scheduled) (body 0) :=
  call_single_match depth program dataHeads runSymbol _ _ _ _ _
    run_ordinary run_known run_arity (dispatch_done _ _ _ _ _) (row_equation 0)

theorem run_done (depth : Nat) (mode reverse lexicals known scheduled : SExpr) :
    run (depth + 1) program dataHeads (runCall mode reverse lexicals known heapNil heapNil scheduled) =
      .complete [runResult known] := by
  rw [run_done_body, done_body]
  apply quote_exact
  simp [runResult, instantiate_atom, variableToken, doneBindings, runTag]

theorem run_rollover_body (depth : Nat) (mode reverse lexicals known node children siblings scheduled : SExpr) :
    run depth program dataHeads (runCall mode reverse lexicals known heapNil (heap node children siblings) scheduled) =
      eval depth program dataHeads (rolloverBindings mode reverse lexicals known node children siblings scheduled) (body 1) :=
  call_single_match depth program dataHeads runSymbol _ _ _ _ _
    run_ordinary run_known run_arity (dispatch_rollover _ _ _ _ _ _ _ _) (row_equation 1)

theorem run_result_inert : inertBinder program dataHeads (runResult (.atom "$result")) = true := by
  have absent : equationsFor "gslt:result:BNFDiscoveryRunV1:111110" program = [] := by rw [equationsFor_program]; rfl
  simp [inertBinder, inertBinders, runResult, reserved, knownFunction, absent, dataHeads, runTag]

theorem rollover_arguments (mode reverse lexicals known node children siblings scheduled : SExpr) :
    instantiateList? (rolloverBindings mode reverse lexicals known node children siblings scheduled)
      [.atom "$mode", .atom "$reverse", .atom "$lexicals", .atom "$known",
        queues (heap (.atom "$node") (.atom "$children") (.atom "$siblings")) heapNil (.atom "$scheduled")] =
      some [mode, reverse, lexicals, known, queues (heap node children siblings) heapNil scheduled] := by
  simp [instantiate_atom, variableToken, rolloverBindings, queues, heap, heapNil]

theorem rollover_recursive_call (depth : Nat) (mode reverse lexicals known node children siblings scheduled : SExpr) :
    eval (depth + 1) program dataHeads (rolloverBindings mode reverse lexicals known node children siblings scheduled)
      (runCall (.atom "$mode") (.atom "$reverse") (.atom "$lexicals") (.atom "$known")
        (heap (.atom "$node") (.atom "$children") (.atom "$siblings")) heapNil (.atom "$scheduled")) =
      run depth program dataHeads
        (runCall mode reverse lexicals known (heap node children siblings) heapNil scheduled) := by
  simp only [runCall, eval]
  have static : dataTemplates dataHeads
      [.atom "$mode", .atom "$reverse", .atom "$lexicals", .atom "$known",
        queues (heap (.atom "$node") (.atom "$children") (.atom "$siblings")) heapNil (.atom "$scheduled")] = true := rfl
  change (if reserved runSymbol || !dataTemplates dataHeads
      [.atom "$mode", .atom "$reverse", .atom "$lexicals", .atom "$known",
        queues (heap (.atom "$node") (.atom "$children") (.atom "$siblings")) heapNil (.atom "$scheduled")]
      then _ else _) = _
  rw [run_ordinary, static]
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [rollover_arguments]
  rfl

theorem rollover_raw_value (depth : Nat) (mode reverse lexicals known node children siblings scheduled : SExpr)
    (answers : List SExpr)
    (recursive : run depth program dataHeads
      (runCall mode reverse lexicals known (heap node children siblings) heapNil scheduled) = .complete answers) :
    eval (depth + 2) program dataHeads (rolloverBindings mode reverse lexicals known node children siblings scheduled)
      (rawWrapper (runCall (.atom "$mode") (.atom "$reverse") (.atom "$lexicals") (.atom "$known")
        (heap (.atom "$node") (.atom "$children") (.atom "$siblings")) heapNil (.atom "$scheduled"))) =
      .complete (.atom "collapse" :: answers) := by
  rw [rawWrapper, literal_superpose]
  have atomAnswer : eval (depth + 1) program dataHeads
      (rolloverBindings mode reverse lexicals known node children siblings scheduled) (.atom "collapse") =
      .complete [.atom "collapse"] := by
    apply atom_exact
    simp [instantiate_atom, variableToken]
  simp [collect, atomAnswer, rollover_recursive_call, recursive]

def rolloverAfter (mode reverse lexicals known node children siblings scheduled value : SExpr) : Bindings :=
  ("$result", encode value) :: rolloverBindings mode reverse lexicals known node children siblings scheduled

theorem rollover_bindings (mode reverse lexicals known node children siblings scheduled : SExpr)
    (values : List SExpr) :
    bindAnswers (rolloverBindings mode reverse lexicals known node children siblings scheduled)
      (runResult (.atom "$result")) (.atom "collapse" :: values.map runResult) =
      values.map (rolloverAfter mode reverse lexicals known node children siblings scheduled) := by
  simp [bindAnswers, bindResult, runResult, runTag, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    rolloverBindings, List.flatMap_map]
  change values.flatMap (fun value =>
    [rolloverAfter mode reverse lexicals known node children siblings scheduled value]) = _
  simp only [← List.map_eq_flatMap]

theorem rollover_quote (depth : Nat) (mode reverse lexicals known node children siblings scheduled value : SExpr) :
    eval (depth + 1) program dataHeads
      (rolloverAfter mode reverse lexicals known node children siblings scheduled value)
      (quote (runResult (.atom "$result"))) = .complete [runResult value] := by
  apply quote_exact
  simp [runResult, instantiate_atom, variableToken, rolloverAfter, runTag]

/-- A real recursive invocation is consumed through the actual literal wrapper
and result binder. Every returned occurrence is retained, including equal ones;
no singleton premise or controller-answer provider appears in this law. -/
theorem rollover_complete (depth : Nat) (mode reverse lexicals known node children siblings scheduled : SExpr)
    (values : List SExpr)
    (recursive : run depth program dataHeads
      (runCall mode reverse lexicals known (heap node children siblings) heapNil scheduled) =
        .complete (values.map runResult)) :
    run (depth + 3) program dataHeads
      (runCall mode reverse lexicals known heapNil (heap node children siblings) scheduled) =
        .complete (values.map runResult) := by
  rw [run_rollover_body, rollover_body]
  change eval (depth + 3) program dataHeads _ (.list [.atom "let", runResult (.atom "$result"), _, _]) = _
  rw [let_complete (depth + 2) program dataHeads _ _ _ _ _ run_result_inert
    (rollover_raw_value depth mode reverse lexicals known node children siblings scheduled _ recursive)]
  rw [rollover_bindings]
  clear recursive
  induction values with
  | nil => rfl
  | cons value tail ih =>
      simp [collect, rollover_quote, ih]

theorem rollover_exhausted (depth : Nat) (mode reverse lexicals known node children siblings scheduled : SExpr)
    (recursive : run depth program dataHeads
      (runCall mode reverse lexicals known (heap node children siblings) heapNil scheduled) = .exhausted) :
    run (depth + 3) program dataHeads
      (runCall mode reverse lexicals known heapNil (heap node children siblings) scheduled) = .exhausted := by
  rw [run_rollover_body, rollover_body]
  change eval (depth + 3) program dataHeads _ (.list [.atom "let", runResult (.atom "$result"), _, _]) = _
  rw [eval]
  rw [run_result_inert]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [rawWrapper, literal_superpose]
  have atomAnswer : eval (depth + 1) program dataHeads
      (rolloverBindings mode reverse lexicals known node children siblings scheduled) (.atom "collapse") =
      .complete [.atom "collapse"] := by
    apply atom_exact
    simp [instantiate_atom, variableToken]
  simp [collect, atomAnswer, rollover_recursive_call, recursive]

def wakeRows : List (Nat × SExpr) := selectedRows wakeSymbol
theorem wake_rows_count : wakeRows.length = 2 := rfl
def wakeRow (index : Fin 2) : Nat × SExpr := wakeRows[index.val]'(by rw [wake_rows_count]; exact index.isLt)
theorem wake_present (index : Fin 2) : (equation? (wakeRow index).2).isSome = true := by fin_cases index <;> rfl
def wakeHead (index : Fin 2) : SExpr := ((equation? (wakeRow index).2).get (wake_present index)).1
def wakeBody (index : Fin 2) : SExpr := ((equation? (wakeRow index).2).get (wake_present index)).2
theorem wake_equation (index : Fin 2) : equation? (wakeRow index).2 = some (wakeHead index, wakeBody index) := by
  fin_cases index <;> rfl
theorem whole_wake_rows : equationsFor wakeSymbol program = [wakeRow 0, wakeRow 1] := by
  rw [equationsFor_program]; rfl

def definitionsNil : SExpr := .atom "BNFDiscoveryDefinitionsNilV1"
def wakeCall (mode candidates origin known lexicals queue : SExpr) : SExpr :=
  .list [.atom wakeSymbol, mode, candidates, origin, known, lexicals, queue]
def wakeResult (value : SExpr) : SExpr := .list [.atom wakeTag, value]
def closureCall (mode candidates reverse lexicals : SExpr) : SExpr :=
  .list [.atom closureSymbol, mode, candidates, reverse, lexicals]
def closureResult (value : SExpr) : SExpr := .list [.atom closureTag, value]
def initialKnown : SExpr := .list [.atom "BNFDiscoveryKnownV1", .atom "BNFGraphTrieEmptyV1", .atom "BNFNamesNilV1"]
def initialQueues : SExpr := queues heapNil heapNil (.atom "BNFGraphTrieEmptyV1")

theorem wake_nil_head : wakeHead 0 = wakeCall (.atom "$mode") definitionsNil (.atom "$origin")
    (.atom "$known") (.atom "$lexicals") (.atom "$queues") := rfl
theorem wake_cons_head : wakeHead 1 = wakeCall (.atom "$mode")
    (.list [.atom "BNFDiscoveryDefinitionsConsV1",
      .list [.atom "BNFDiscoveryDefinitionV1", .atom "$rank", .atom "$name", .atom "$expression", .atom "$span"],
      .atom "$rest"]) (.atom "$origin") (.atom "$known") (.atom "$lexicals")
    (queues (.atom "$current") (.atom "$following") (.atom "$scheduled")) := rfl
theorem wake_nil_body : wakeBody 0 = quote (wakeResult (.atom "$queues")) := rfl
theorem closure_head : head 3 = closureCall (.atom "$mode") (.atom "$ranked") (.atom "$reverse") (.atom "$lexicals") := rfl
theorem closure_body : body 3 =
    letTerm (wakeResult (.atom "$initial"))
      (rawWrapper (wakeCall (.atom "$mode") (.atom "$ranked") (.atom "BNFDiscoveryInitialV1")
        initialKnown (.atom "$lexicals") initialQueues))
      (letTerm (runResult (.atom "$result"))
        (rawWrapper (.list [.atom runSymbol, .atom "$mode", .atom "$reverse", .atom "$lexicals", initialKnown, .atom "$initial"]))
        (quote (closureResult (.atom "$result")))) := rfl

def wakeBindings (mode origin known lexicals queue : SExpr) : Bindings :=
  [("$known", encode known), ("$queues", encode queue), ("$lexicals", encode lexicals),
    ("$origin", encode origin), ("$mode", encode mode)]
def closureBindings (mode candidates reverse lexicals : SExpr) : Bindings :=
  [("$ranked", encode candidates), ("$lexicals", encode lexicals), ("$reverse", encode reverse), ("$mode", encode mode)]

theorem dispatch_wake_nil (mode origin known lexicals queue : SExpr) :
    dispatch [] (wakeCall mode definitionsNil origin known lexicals queue) program =
      [(wakeRow 0, wakeBindings mode origin known lexicals queue)] := by
  rw [show wakeCall mode definitionsNil origin known lexicals queue =
      .list (.atom wakeSymbol :: [mode, definitionsNil, origin, known, lexicals, queue]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, whole_wake_rows]
  simp [dispatch, matchEquation, wake_equation, wake_nil_head, wake_cons_head,
    wakeCall, definitionsNil, queues, wakeSymbol, bindResult, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, wakeBindings]

theorem dispatch_closure (mode candidates reverse lexicals : SExpr) :
    dispatch [] (closureCall mode candidates reverse lexicals) program =
      [(row 3, closureBindings mode candidates reverse lexicals)] := by
  rw [show closureCall mode candidates reverse lexicals =
      .list (.atom closureSymbol :: [mode, candidates, reverse, lexicals]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, whole_closure_rows]
  simp [dispatch, matchEquation, row_equation, closure_head, closureCall, closureSymbol,
    bindResult, template, templates, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, closureBindings]

theorem wake_known : knownFunction program wakeSymbol = true := by rw [knownFunction, whole_wake_rows]; rfl
theorem wake_arity : hasArity program wakeSymbol 6 = true := by
  rw [hasArity, whole_wake_rows]; simp [wake_equation, wake_nil_head, wakeCall]
theorem closure_known : knownFunction program closureSymbol = true := by rw [knownFunction, whole_closure_rows]; rfl
theorem closure_arity : hasArity program closureSymbol 4 = true := by
  rw [hasArity, whole_closure_rows]; simp [row_equation, closure_head, closureCall]

theorem wake_nil (depth : Nat) (mode origin known lexicals queue : SExpr) :
    run (depth + 1) program dataHeads (wakeCall mode definitionsNil origin known lexicals queue) =
      .complete [wakeResult queue] := by
  change run (depth + 1) program dataHeads
    (.list [.atom wakeSymbol, mode, definitionsNil, origin, known, lexicals, queue]) = _
  rw [call_single_match (depth + 1) program dataHeads wakeSymbol
    [mode, definitionsNil, origin, known, lexicals, queue] _ _ _ _
    (by rfl) wake_known wake_arity (dispatch_wake_nil _ _ _ _ _) (wake_equation 0), wake_nil_body]
  apply quote_exact
  simp [wakeResult, instantiate_atom, variableToken, wakeBindings, wakeTag]

theorem run_closure_body (depth : Nat) (mode candidates reverse lexicals : SExpr) :
    run depth program dataHeads (closureCall mode candidates reverse lexicals) =
      eval depth program dataHeads (closureBindings mode candidates reverse lexicals) (body 3) :=
  call_single_match depth program dataHeads closureSymbol _ _ _ _ _
    (by rfl) closure_known closure_arity (dispatch_closure _ _ _ _) (row_equation 3)

theorem wake_nil_source_to_actual :
    ((PlainBnfWakeSourceExecution.rows.take 1).mapM clause?) = some [(wakeRow 0).2] := rfl

theorem wake_result_inert : inertBinder program dataHeads (wakeResult (.atom "$initial")) = true := by
  have absent : equationsFor "gslt:result:BNFDiscoveryWakeV1:1111110" program = [] := by rw [equationsFor_program]; rfl
  simp [inertBinder, inertBinders, wakeResult, reserved, knownFunction, absent, dataHeads, wakeTag]

def initialWakeTemplate : SExpr := wakeCall (.atom "$mode") (.atom "$ranked") (.atom "BNFDiscoveryInitialV1")
  initialKnown (.atom "$lexicals") initialQueues
def initialRunTemplate : SExpr :=
  .list [.atom runSymbol, .atom "$mode", .atom "$reverse", .atom "$lexicals", initialKnown, .atom "$initial"]

theorem initial_wake_call (depth : Nat) (mode reverse lexicals : SExpr) :
    eval (depth + 2) program dataHeads (closureBindings mode definitionsNil reverse lexicals) initialWakeTemplate =
      .complete [wakeResult initialQueues] := by
  simp only [initialWakeTemplate, wakeCall, eval]
  have static : dataTemplates dataHeads [.atom "$mode", .atom "$ranked", .atom "BNFDiscoveryInitialV1",
      initialKnown, .atom "$lexicals", initialQueues] = true := rfl
  have ordinary : reserved wakeSymbol = false := rfl
  rw [ordinary, static]
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have arguments : instantiateList? (closureBindings mode definitionsNil reverse lexicals)
      [.atom "$mode", .atom "$ranked", .atom "BNFDiscoveryInitialV1", initialKnown, .atom "$lexicals", initialQueues] =
      some [mode, definitionsNil, .atom "BNFDiscoveryInitialV1", initialKnown, lexicals, initialQueues] := by
    simp [instantiate_atom, variableToken, closureBindings, initialKnown, initialQueues, queues, heapNil]
  rw [arguments]
  exact wake_nil depth mode (.atom "BNFDiscoveryInitialV1") initialKnown lexicals initialQueues

theorem initial_wake_value (depth : Nat) (mode reverse lexicals : SExpr) :
    eval (depth + 3) program dataHeads (closureBindings mode definitionsNil reverse lexicals)
      (rawWrapper initialWakeTemplate) = .complete [.atom "collapse", wakeResult initialQueues] := by
  rw [rawWrapper, literal_superpose]
  have atomAnswer : eval (depth + 2) program dataHeads (closureBindings mode definitionsNil reverse lexicals)
      (.atom "collapse") = .complete [.atom "collapse"] := by
    apply atom_exact
    simp [instantiate_atom, variableToken]
  simp [collect, atomAnswer, initial_wake_call]

def closureAfter (mode reverse lexicals : SExpr) : Bindings :=
  ("$initial", encode initialQueues) :: closureBindings mode definitionsNil reverse lexicals

theorem initial_wake_binding (mode reverse lexicals : SExpr) :
    bindAnswers (closureBindings mode definitionsNil reverse lexicals) (wakeResult (.atom "$initial"))
      [.atom "collapse", wakeResult initialQueues] = [closureAfter mode reverse lexicals] := by
  simp [bindAnswers, bindResult, wakeResult, wakeTag, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, closureBindings, closureAfter]

theorem initial_run_call (depth : Nat) (mode reverse lexicals : SExpr) :
    eval (depth + 2) program dataHeads (closureAfter mode reverse lexicals) initialRunTemplate =
      .complete [runResult initialKnown] := by
  simp only [initialRunTemplate, eval]
  have static : dataTemplates dataHeads [.atom "$mode", .atom "$reverse", .atom "$lexicals",
      initialKnown, .atom "$initial"] = true := rfl
  rw [run_ordinary, static]
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have arguments : instantiateList? (closureAfter mode reverse lexicals)
      [.atom "$mode", .atom "$reverse", .atom "$lexicals", initialKnown, .atom "$initial"] =
      some [mode, reverse, lexicals, initialKnown, initialQueues] := by
    simp [instantiate_atom, variableToken, closureAfter, closureBindings, initialKnown]
  rw [arguments]
  exact run_done depth mode reverse lexicals initialKnown (.atom "BNFGraphTrieEmptyV1")

theorem initial_run_value (depth : Nat) (mode reverse lexicals : SExpr) :
    eval (depth + 3) program dataHeads (closureAfter mode reverse lexicals)
      (rawWrapper initialRunTemplate) = .complete [.atom "collapse", runResult initialKnown] := by
  rw [rawWrapper, literal_superpose]
  have atomAnswer : eval (depth + 2) program dataHeads (closureAfter mode reverse lexicals)
      (.atom "collapse") = .complete [.atom "collapse"] := by
    apply atom_exact
    simp [instantiate_atom, variableToken]
  simp [collect, atomAnswer, initial_run_call]

def closureFinal (mode reverse lexicals : SExpr) : Bindings :=
  ("$result", encode initialKnown) :: closureAfter mode reverse lexicals

theorem initial_run_binding (mode reverse lexicals : SExpr) :
    bindAnswers (closureAfter mode reverse lexicals) (runResult (.atom "$result"))
      [.atom "collapse", runResult initialKnown] = [closureFinal mode reverse lexicals] := by
  simp [bindAnswers, bindResult, runResult, runTag, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    closureAfter, closureBindings, closureFinal]

/-- This helper case really executes the generated Wake and Run calls.
Empty candidates are not a claim that an empty grammar passes admission. -/
theorem closure_empty (depth : Nat) (mode reverse lexicals : SExpr) :
    run (depth + 5) program dataHeads (closureCall mode definitionsNil reverse lexicals) =
      .complete [closureResult initialKnown] := by
  rw [run_closure_body, closure_body]
  change eval (depth + 5) program dataHeads _
    (.list [.atom "let", wakeResult (.atom "$initial"), rawWrapper initialWakeTemplate,
      .list [.atom "let", runResult (.atom "$result"), rawWrapper initialRunTemplate,
        quote (closureResult (.atom "$result"))]]) = _
  rw [let_complete (depth + 4) program dataHeads _ _ _ _ _ wake_result_inert
    (initial_wake_value (depth + 1) mode reverse lexicals), initial_wake_binding, collect_singleton]
  rw [let_complete (depth + 3) program dataHeads _ _ _ _ _ run_result_inert
    (initial_run_value depth mode reverse lexicals), initial_run_binding, collect_singleton]
  apply quote_exact
  simp [instantiate_atom, variableToken, closureResult, closureFinal, closureTag]

/-- The same literal name with an extra pair of parentheses does not match
the atom used by the actual empty-heap clauses. -/
theorem nullary_nil_not_done (mode reverse lexicals known scheduled : SExpr) :
    dispatch [] (runCall mode reverse lexicals known (.list [heapNil]) heapNil scheduled) program = [] := by
  rw [show runCall mode reverse lexicals known (.list [heapNil]) heapNil scheduled =
      .list (.atom runSymbol :: [mode, reverse, lexicals, known, queues (.list [heapNil]) heapNil scheduled]) from rfl,
    dispatch_literal_filter [] _ _ program literal_heads, whole_run_rows]
  simp [dispatch, matchEquation, row_equation, done_head, rollover_head, publish_head,
    runCall, heapNil, heap, queues, runSymbol, bindResult, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem closure_short_is_exhausted (mode reverse lexicals : SExpr) :
    run 1 program dataHeads (closureCall mode definitionsNil reverse lexicals) = .exhausted := by
  rw [run_closure_body, closure_body]
  change eval 1 program dataHeads _ (.list [.atom "let", wakeResult (.atom "$initial"), _, _]) = _
  simp [eval, wake_result_inert]

/-- Equal history occurrences and executable-looking payloads stay opaque
through the actual done quotation. -/
theorem opaque_duplicate_payloads (mode reverse lexicals scheduled value : SExpr) :
    run 1 program dataHeads
      (runCall mode reverse lexicals (.list [.atom "quote", value, value]) heapNil heapNil scheduled) =
      .complete [runResult (.list [.atom "quote", value, value])] := run_done 0 _ _ _ _ _

/-- Repeating the actual done equation creates a second matching occurrence;
the complete program filter cannot silently discard it. -/
theorem duplicated_done_occurrences (mode reverse lexicals known scheduled : SExpr) :
    dispatch [] (runCall mode reverse lexicals known heapNil heapNil scheduled) (program ++ [row 0]) =
      [(row 0, doneBindings mode reverse lexicals known scheduled),
       (row 0, doneBindings mode reverse lexicals known scheduled)] := by
  rw [dispatch_append, dispatch_done]
  simp [dispatch, matchEquation, row_equation, done_head, runCall, heapNil, queues, runSymbol,
    bindResult, template, templates, variableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, doneBindings]

#print axioms source_to_actual_equations
#print axioms run_done
#print axioms rollover_complete
#print axioms rollover_exhausted
#print axioms closure_empty
#print axioms nullary_nil_not_done
#print axioms closure_short_is_exhausted
#print axioms opaque_duplicate_payloads
#print axioms duplicated_done_occurrences

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedControllerSource
