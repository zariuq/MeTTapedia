import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarListSyntax
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedUnicodeScalarExecution
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderExecution
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedDiagnosticsAppendExecution
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDepthMonotonicity

/-!
# Execution of the actual recursive scalar-list caller

The independent observation is the ordered sequence of Unicode and adjacent
ordering diagnostics. Execution refers to the complete generated fixture and
its original recursive clauses. Worker equations, result binding, and append
execute in the existing finite ground model; none is replaced by a provider
returning the observation. This selected model is not native-runtime adequacy.

Inputs are canonical encodings of mathematical Integer lists, with arbitrary
opaque origin data. The equation inventory is fixed; imports are not executed.
The result does not cover every structurally typed input spelling, machine
integer representation, effectful context, or changing runtime inventory.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarListExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult bindAnswers)
open GeneratedPeTTaTemplateInstantiation
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open PlainBnfGeneratedScalarOrderSyntax (program equationsFor_program)
open PlainBnfLexicalScalarSemantics (isUnicodeScalarInt)


def unicodeDiagnostics (scalar : Int) (origin : SExpr) : List SExpr :=
  if isUnicodeScalarInt scalar then [] else
    [.list [.atom "BNFInvalidUnicodeScalarV1", .atom (toString scalar), origin]]

def orderDiagnostics (first next : Int) (origin : SExpr) : List SExpr :=
  if first < next then [] else
    [.list [.atom "BNFNonIncreasingLexicalScalarsV1",
      .atom (toString first), .atom (toString next), origin]]

def diagnostics : List Int → SExpr → List SExpr
  | [], _ => []
  | [scalar], origin => unicodeDiagnostics scalar origin
  | first :: next :: rest, origin =>
      unicodeDiagnostics first origin ++ orderDiagnostics first next origin ++
        diagnostics (next :: rest) origin

/-- Empty input has no worker clause; it must not become a successful verdict. -/
def answers (values : List Int) (origin : SExpr) : List SExpr :=
  if values.isEmpty then [] else [PlainBnfGeneratedScalarListSyntax.result (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (diagnostics values origin))]

def dataHeads : List String := PlainBnfGeneratedUnicodeScalarExecution.dataHeads ++ PlainBnfGeneratedScalarOrderExecution.dataHeads ++ PlainBnfGeneratedDiagnosticsAppendExecution.dataHeads ++
  [PlainBnfGeneratedScalarListSyntax.tag, "bnf-v1:scalars-cons", "bnf-v1:scalars-nil"]

theorem unicode_length (scalar : Int) (origin : SExpr) :
    (unicodeDiagnostics scalar origin).length ≤ 1 := by
  simp only [unicodeDiagnostics]; split <;> simp

theorem order_length (first next : Int) (origin : SExpr) :
    (orderDiagnostics first next origin).length ≤ 1 := by
  simp only [orderDiagnostics]; split <;> simp

private theorem unicode_extension :
    GeneratedPeTTaDataHeadExtension.Extends PlainBnfGeneratedUnicodeScalarExecution.dataHeads dataHeads := by
  intro head present
  simpa only [dataHeads, List.contains_append, Bool.or_eq_true] using
    Or.inl (Or.inl (Or.inl present))

private theorem order_extension :
    GeneratedPeTTaDataHeadExtension.Extends PlainBnfGeneratedScalarOrderExecution.dataHeads dataHeads := by
  intro head present
  simpa only [dataHeads, List.contains_append, Bool.or_eq_true] using
    Or.inl (Or.inl (Or.inr present))

private theorem append_extension :
    GeneratedPeTTaDataHeadExtension.Extends PlainBnfGeneratedDiagnosticsAppendExecution.dataHeads dataHeads := by
  intro head present
  simpa only [dataHeads, List.contains_append, Bool.or_eq_true] using
    Or.inl (Or.inr present)

theorem unicode_run (extra : Nat) (typed : Bool) (scalar : Int) (origin : SExpr) :
    run (extra + 7) program dataHeads (PlainBnfGeneratedUnicodeScalarExecution.call typed scalar origin) =
      .complete [PlainBnfGeneratedUnicodeScalarExecution.result (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (unicodeDiagnostics scalar origin))] := by
  have completed := GeneratedPeTTaDataHeadExtension.run_completed unicode_extension
    (extra + 7) program _ _ (PlainBnfGeneratedUnicodeScalarExecution.run_exact extra typed scalar origin)
  cases valid : isUnicodeScalarInt scalar <;>
    simpa [valid, PlainBnfGeneratedUnicodeScalarExecution.answer, unicodeDiagnostics, PlainBnfGeneratedUnicodeScalarExecution.diagnostic, PlainBnfGeneratedUnicodeScalarExecution.result,
    PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics, PlainBnfGeneratedDiagnosticsAppendExecution.nil, PlainBnfGeneratedDiagnosticsAppendExecution.cons] using completed

theorem order_run (extra : Nat) (typed : Bool) (first next : Int) (origin : SExpr) :
    run (extra + 4) program dataHeads (PlainBnfGeneratedScalarOrderExecution.call typed first next origin) =
      .complete [PlainBnfGeneratedScalarOrderExecution.result (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (orderDiagnostics first next origin))] := by
  have completed := GeneratedPeTTaDataHeadExtension.run_completed order_extension
    (extra + 4) program _ _ (PlainBnfGeneratedScalarOrderExecution.run_exact extra typed first next origin)
  by_cases increasing : first < next <;>
    simpa [increasing, PlainBnfGeneratedScalarOrderExecution.answer, orderDiagnostics, PlainBnfGeneratedScalarOrderExecution.diagnostic, PlainBnfGeneratedScalarOrderExecution.result,
    PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics, PlainBnfGeneratedDiagnosticsAppendExecution.nil, PlainBnfGeneratedDiagnosticsAppendExecution.cons] using completed

theorem append_run (depth : Nat) (typed : Bool) (left right : List SExpr)
    (enough : 2 * left.length < depth) :
    run depth program dataHeads (PlainBnfGeneratedDiagnosticsAppendExecution.call typed (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics left) (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics right)) =
      .complete [PlainBnfGeneratedDiagnosticsAppendExecution.result (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (left ++ right))] := by
  apply GeneratedPeTTaDataHeadExtension.run_completed append_extension
  simp [PlainBnfGeneratedDiagnosticsAppendExecution.run_exact, enough, PlainBnfGeneratedDiagnosticsAppendExecution.prepend_diagnostics]

private theorem call_template (depth : Nat) (env : Bindings)
    (head : String) (arguments values : List SExpr)
    (ordinary : reserved head = false)
    (data : dataTemplates dataHeads arguments = true)
    (closed : instantiateList? env arguments = some values) :
    eval (depth + 1) program dataHeads env (.list (.atom head :: arguments)) =
      run depth program dataHeads (.list (.atom head :: values)) := by
  rw [eval]
  split <;> simp_all [reserved, run]
  all_goals intros; subst_vars; simp [reserved] at ordinary

private def tagged (tag : String) (payload : SExpr) : SExpr :=
  .list [.atom tag, payload]

private def literal (inner : SExpr) : SExpr :=
  .list [.atom "superpose", .list [.atom "collapse", inner]]

private theorem literal_complete (depth : Nat) (env : Bindings) (inner value : SExpr)
    (completed : eval (depth + 1) program dataHeads env inner = .complete [value]) :
    eval (depth + 2) program dataHeads env (literal inner) =
      .complete [.atom "collapse", value] := by
  rw [literal, literal_superpose]
  have atomDone : eval (depth + 1) program dataHeads env (.atom "collapse") =
      .complete [.atom "collapse"] := by
    apply atom_exact
    simp [instantiate_atom, variableToken]
  simp [collect, atomDone, completed]

private theorem bind_tag (env : Bindings) (tag name : String) (payload : SExpr)
    (tagLiteral : variableToken tag = false) (named : variableToken name = true)
    (fresh : env.find? (·.1 == name) = none) :
    bindAnswers env (tagged tag (.atom name)) [tagged tag payload] =
      [(name, encode payload) :: env] := by
  simp [bindAnswers, bindResult, tagged, template, templates, tagLiteral, named,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, fresh]

private theorem bind_literal_tag (env : Bindings) (tag name : String) (payload : SExpr)
    (tagLiteral : variableToken tag = false) (named : variableToken name = true)
    (fresh : env.find? (·.1 == name) = none) :
    bindAnswers env (tagged tag (.atom name)) [.atom "collapse", tagged tag payload] =
      [(name, encode payload) :: env] := by
  have mismatch : bindResult env (tagged tag (.atom name)) (.atom "collapse") = [] := by
    simp [bindResult, tagged, template, encode, matchPattern]
  simp only [bindAnswers, List.flatMap_cons, List.flatMap_nil, List.append_nil] at *
  rw [mismatch, List.nil_append]
  simpa [bindAnswers] using bind_tag env tag name payload tagLiteral named fresh

private theorem inert_tag (tag name : String)
    (ordinary : reserved tag = false) (absent : equationsFor tag program = [])
    (present : dataHeads.contains tag = true) (named : name ≠ "$_") :
    inertBinder program dataHeads (tagged tag (.atom name)) = true := by
  simp [tagged, inertBinder, inertBinders, ordinary, knownFunction, absent, named]
  simpa using present

private theorem worker_inert (tag name : String)
    (member : tag ∈ [PlainBnfGeneratedUnicodeScalarExecution.tag,
      PlainBnfGeneratedScalarOrderSyntax.tag,
      PlainBnfGeneratedDiagnosticsAppendExecution.tag, PlainBnfGeneratedScalarListSyntax.tag])
    (named : name ≠ "$_") :
    inertBinder program dataHeads (tagged tag (.atom name)) = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals refine inert_tag _ name (by rfl) ?_ (by rfl) named
  all_goals rw [equationsFor_program]; rfl

private theorem let_literal (depth : Nat) (env : Bindings)
    (tag name : String) (inner payload continuation : SExpr)
    (inert : inertBinder program dataHeads (tagged tag (.atom name)) = true)
    (tagLiteral : variableToken tag = false) (named : variableToken name = true)
    (fresh : env.find? (·.1 == name) = none)
    (completed : eval (depth + 1) program dataHeads env inner = .complete [tagged tag payload]) :
    eval (depth + 3) program dataHeads env
      (.list [.atom "let", tagged tag (.atom name), literal inner, continuation]) =
        eval (depth + 2) program dataHeads ((name, encode payload) :: env) continuation := by
  rw [let_complete (depth + 2) program dataHeads _ _ _ _ _ inert
    (literal_complete depth env inner (tagged tag payload) completed)]
  rw [bind_literal_tag env tag name payload tagLiteral named fresh, collect_singleton]

private theorem let_once (depth : Nat) (env : Bindings)
    (tag name : String) (inner payload continuation : SExpr)
    (inert : inertBinder program dataHeads (tagged tag (.atom name)) = true)
    (tagLiteral : variableToken tag = false) (named : variableToken name = true)
    (fresh : env.find? (·.1 == name) = none)
    (completed : eval (depth + 1) program dataHeads env inner = .complete [tagged tag payload]) :
    eval (depth + 3) program dataHeads env
      (.list [.atom "let", tagged tag (.atom name),
        .list [.atom "once", inner], continuation]) =
        eval (depth + 2) program dataHeads ((name, encode payload) :: env) continuation := by
  have single := once_complete (depth + 1) program dataHeads env inner [tagged tag payload]
    (by simp) completed
  simp only [List.take_succ_cons, List.take_zero] at single
  rw [let_complete (depth + 2) program dataHeads _ _ _ _ _ inert single]
  rw [bind_tag env tag name payload tagLiteral named fresh, collect_singleton]

theorem singleton_run (extra : Nat) (typed : Bool) (scalar : Int) (origin : SExpr) :
    run (extra + 10) program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [scalar]) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (unicodeDiagnostics scalar origin))] := by
  rw [PlainBnfGeneratedScalarListSyntax.run_single,
    PlainBnfGeneratedScalarListSyntax.singleton_body]
  have inner := call_template (extra + 7)
    (PlainBnfGeneratedScalarListSyntax.singletonEnv scalar origin)
    (PlainBnfGeneratedScalarListSyntax.scalarSymbol typed)
    [.atom "$scalar", .atom "$origin"] [.atom (toString scalar), origin]
    (by cases typed <;> rfl) (by rfl)
    (by simp [instantiate_atom, variableToken, PlainBnfGeneratedScalarListSyntax.singletonEnv])
  have completed := inner.trans (unicode_run extra typed scalar origin)
  change eval (extra + 7 + 3) program dataHeads _
    (.list [.atom "let", tagged PlainBnfGeneratedUnicodeScalarExecution.tag (.atom "$diagnostics"),
      literal (.list [.atom (PlainBnfGeneratedScalarListSyntax.scalarSymbol typed),
        .atom "$scalar", .atom "$origin"]), _]) = _
  rw [let_literal (extra + 7) _ _ "$diagnostics" _ _ _
    (worker_inert _ _ (by simp) (by decide))
    (by simp [variableToken, PlainBnfGeneratedUnicodeScalarExecution.tag])
    (by simp [variableToken])
    (by simp [PlainBnfGeneratedScalarListSyntax.singletonEnv]) completed]
  apply quote_exact
  simp [instantiate_atom, variableToken, PlainBnfGeneratedScalarListSyntax.result,
    PlainBnfGeneratedScalarListSyntax.tag]

/-- The two actual wrappers have different intermediate answers. The raw
literal atom is filtered by the subsequent inert result binder; it is not
erased by pretending that the two wrapper expressions are equivalent. -/
theorem order_wrapper_answers (extra : Nat) (typed : Bool) (env : Bindings)
    (first next : Int) (origin : SExpr)
    (closed : instantiateList? env [.atom "$head", .atom "$next", .atom "$origin"] =
      some [.atom (toString first), .atom (toString next), origin]) :
    eval (extra + 6) program dataHeads env
      (PlainBnfGeneratedScalarListSyntax.orderCallTemplate typed) =
      .complete (if typed then
        [PlainBnfGeneratedScalarOrderExecution.result
          (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (orderDiagnostics first next origin))]
      else [.atom "collapse", PlainBnfGeneratedScalarOrderExecution.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (orderDiagnostics first next origin))]) := by
  have inner := call_template (extra + 4) env (PlainBnfGeneratedScalarOrderSyntax.symbol typed)
    _ _ (by cases typed <;> rfl) (by rfl) closed
  have completed := inner.trans (order_run extra typed first next origin)
  cases typed
  · simpa only [PlainBnfGeneratedScalarListSyntax.orderCallTemplate, Bool.false_eq_true,
      ↓reduceIte, Nat.add_assoc, literal] using literal_complete (extra + 4) env _ _ completed
  · simpa only [PlainBnfGeneratedScalarListSyntax.orderCallTemplate, ↓reduceIte,
      Nat.add_assoc, List.take_succ_cons, List.take_zero] using
      once_complete (extra + 5) program dataHeads env _ _ (by simp) completed

private theorem order_let (extra : Nat) (typed : Bool) (env : Bindings)
    (first next : Int) (origin continuation : SExpr)
    (closed : instantiateList? env [.atom "$head", .atom "$next", .atom "$origin"] =
      some [.atom (toString first), .atom (toString next), origin])
    (fresh : env.find? (·.1 == "$orderDiagnostics") = none) :
    eval (extra + 7) program dataHeads env
      (.list [.atom "let", tagged PlainBnfGeneratedScalarOrderSyntax.tag (.atom "$orderDiagnostics"),
        PlainBnfGeneratedScalarListSyntax.orderCallTemplate typed, continuation]) =
      eval (extra + 6) program dataHeads
        (("$orderDiagnostics", encode (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
          (orderDiagnostics first next origin))) :: env) continuation := by
  have inner := call_template (extra + 4) env (PlainBnfGeneratedScalarOrderSyntax.symbol typed)
    _ _ (by cases typed <;> rfl) (by rfl) closed
  have completed := inner.trans (order_run extra typed first next origin)
  have inert := worker_inert PlainBnfGeneratedScalarOrderSyntax.tag "$orderDiagnostics"
    (by simp) (by decide)
  have tagLiteral : variableToken PlainBnfGeneratedScalarOrderSyntax.tag = false := by
    simp [variableToken, PlainBnfGeneratedScalarOrderSyntax.tag]
  have named : variableToken "$orderDiagnostics" = true := by simp [variableToken]
  cases typed
  · simpa only [PlainBnfGeneratedScalarListSyntax.orderCallTemplate, Bool.false_eq_true,
      ↓reduceIte, Nat.add_assoc, literal] using
      let_literal (extra + 4) env _ _ _ _ continuation inert tagLiteral named fresh completed
  · simpa only [PlainBnfGeneratedScalarListSyntax.orderCallTemplate,
      ↓reduceIte, Nat.add_assoc] using
      let_once (extra + 4) env _ _ _ _ continuation inert tagLiteral named fresh completed

theorem cons_run (depth : Nat) (typed : Bool) (first next : Int)
    (tail origin : SExpr) (tailDiagnostics : List SExpr)
    (recursive : run (depth + 7) program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.cons (.atom (toString next)) tail) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics tailDiagnostics)]) :
    run (depth + 12) program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.cons (.atom (toString first))
          (PlainBnfGeneratedScalarListSyntax.cons (.atom (toString next)) tail)) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
          (unicodeDiagnostics first origin ++ orderDiagnostics first next origin ++ tailDiagnostics))] := by
  let headDs := PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (unicodeDiagnostics first origin)
  let orderDs := PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics (orderDiagnostics first next origin)
  let tailDs := PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics tailDiagnostics
  let currentDs := PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
    (unicodeDiagnostics first origin ++ orderDiagnostics first next origin)
  let allDs := PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
    (unicodeDiagnostics first origin ++ orderDiagnostics first next origin ++ tailDiagnostics)
  let env0 := PlainBnfGeneratedScalarListSyntax.consEnv first next tail origin
  let env1 := ("$headDiagnostics", encode headDs) :: env0
  let env2 := ("$orderDiagnostics", encode orderDs) :: env1
  let env3 := ("$tailDiagnostics", encode tailDs) :: env2
  let env4 := ("$currentDiagnostics", encode currentDs) :: env3
  rw [PlainBnfGeneratedScalarListSyntax.run_cons, PlainBnfGeneratedScalarListSyntax.cons_body]
  have scalarCall := call_template (depth + 9) env0
    (PlainBnfGeneratedScalarListSyntax.scalarSymbol typed)
    [.atom "$head", .atom "$origin"] [.atom (toString first), origin]
    (by cases typed <;> rfl) (by rfl)
    (by simp [instantiate_atom, variableToken, env0, PlainBnfGeneratedScalarListSyntax.consEnv])
  have scalarDone : eval (depth + 10) program dataHeads env0
      (.list [.atom (PlainBnfGeneratedScalarListSyntax.scalarSymbol typed),
        .atom "$head", .atom "$origin"]) =
      .complete [tagged PlainBnfGeneratedUnicodeScalarExecution.tag headDs] :=
    scalarCall.trans (unicode_run (depth + 2) typed first origin)
  change eval (depth + 9 + 3) program dataHeads env0
    (.list [.atom "let", tagged PlainBnfGeneratedUnicodeScalarExecution.tag (.atom "$headDiagnostics"),
      literal (.list [.atom (PlainBnfGeneratedScalarListSyntax.scalarSymbol typed),
        .atom "$head", .atom "$origin"]), _]) = _
  rw [let_literal (depth + 9) env0 _ "$headDiagnostics" _ headDs _
    (worker_inert _ _ (by simp) (by decide))
    (by simp [variableToken, PlainBnfGeneratedUnicodeScalarExecution.tag])
    (by simp [variableToken])
    (by simp [env0, PlainBnfGeneratedScalarListSyntax.consEnv]) scalarDone]
  change eval (depth + 4 + 7) program dataHeads env1
    (.list [.atom "let", tagged PlainBnfGeneratedScalarOrderSyntax.tag (.atom "$orderDiagnostics"),
      PlainBnfGeneratedScalarListSyntax.orderCallTemplate typed, _]) = _
  rw [order_let (depth + 4) typed env1 first next origin _
    (by simp [instantiate_atom, variableToken, env1, env0, PlainBnfGeneratedScalarListSyntax.consEnv])
    (by simp [env1, env0, PlainBnfGeneratedScalarListSyntax.consEnv])]
  have tailCall := call_template (depth + 7) env2 (PlainBnfGeneratedScalarListSyntax.symbol typed)
    [PlainBnfGeneratedScalarListSyntax.cons (.atom "$next") (.atom "$tail"), .atom "$origin"]
    [PlainBnfGeneratedScalarListSyntax.cons (.atom (toString next)) tail, origin]
    (PlainBnfGeneratedScalarListSyntax.ordinary typed) (by rfl)
    (by simp [instantiate_atom, variableToken, env2, env1, env0,
      PlainBnfGeneratedScalarListSyntax.consEnv, PlainBnfGeneratedScalarListSyntax.cons])
  have tailDone := tailCall.trans recursive
  change eval (depth + 7 + 3) program dataHeads env2
    (.list [.atom "let", tagged PlainBnfGeneratedScalarListSyntax.tag (.atom "$tailDiagnostics"),
      literal (.list [.atom (PlainBnfGeneratedScalarListSyntax.symbol typed),
        PlainBnfGeneratedScalarListSyntax.cons (.atom "$next") (.atom "$tail"), .atom "$origin"]), _]) = _
  rw [let_literal (depth + 7) env2 _ "$tailDiagnostics" _ tailDs _
    (worker_inert _ _ (by simp) (by decide))
    (by simp [variableToken, PlainBnfGeneratedScalarListSyntax.tag])
    (by simp [variableToken])
    (by simp [env2, env1, env0, PlainBnfGeneratedScalarListSyntax.consEnv]) tailDone]
  have currentCall := call_template (depth + 6) env3 (PlainBnfGeneratedScalarListSyntax.appendSymbol typed)
    [.atom "$headDiagnostics", .atom "$orderDiagnostics"] [headDs, orderDs]
    (by cases typed <;> rfl) (by rfl)
    (by simp [instantiate_atom, variableToken, env3, env2, env1])
  have appendSymbol : PlainBnfGeneratedScalarListSyntax.appendSymbol typed =
      PlainBnfGeneratedDiagnosticsAppendExecution.symbol typed := by cases typed <;> rfl
  have currentRun := append_run (depth + 6) typed
    (unicodeDiagnostics first origin) (orderDiagnostics first next origin)
    (by have small := unicode_length first origin; omega)
  rw [PlainBnfGeneratedDiagnosticsAppendExecution.call, ← appendSymbol] at currentRun
  have currentDone := currentCall.trans currentRun
  change eval (depth + 6 + 3) program dataHeads env3
    (.list [.atom "let", tagged PlainBnfGeneratedDiagnosticsAppendExecution.tag (.atom "$currentDiagnostics"),
      .list [.atom "once", .list [.atom (PlainBnfGeneratedScalarListSyntax.appendSymbol typed),
        .atom "$headDiagnostics", .atom "$orderDiagnostics"]], _]) = _
  rw [let_once (depth + 6) env3 _ "$currentDiagnostics" _ currentDs _
    (worker_inert _ _ (by simp) (by decide))
    (by simp [variableToken, PlainBnfGeneratedDiagnosticsAppendExecution.tag])
    (by simp [variableToken])
    (by simp [env3, env2, env1, env0, PlainBnfGeneratedScalarListSyntax.consEnv]) currentDone]
  have allCall := call_template (depth + 5) env4 (PlainBnfGeneratedScalarListSyntax.appendSymbol typed)
    [.atom "$currentDiagnostics", .atom "$tailDiagnostics"] [currentDs, tailDs]
    (by cases typed <;> rfl) (by rfl)
    (by simp [instantiate_atom, variableToken, env4, env3])
  have allRun := append_run (depth + 5) typed
    (unicodeDiagnostics first origin ++ orderDiagnostics first next origin) tailDiagnostics
    (by have h := unicode_length first origin; have o := order_length first next origin
        simp only [List.length_append]; omega)
  rw [PlainBnfGeneratedDiagnosticsAppendExecution.call, ← appendSymbol] at allRun
  have allDone := allCall.trans allRun
  change eval (depth + 5 + 3) program dataHeads env4
    (.list [.atom "let", tagged PlainBnfGeneratedDiagnosticsAppendExecution.tag (.atom "$diagnostics"),
      .list [.atom "once", .list [.atom (PlainBnfGeneratedScalarListSyntax.appendSymbol typed),
        .atom "$currentDiagnostics", .atom "$tailDiagnostics"]], _]) = _
  rw [let_once (depth + 5) env4 _ "$diagnostics" _ allDs _
    (worker_inert _ _ (by simp) (by decide))
    (by simp [variableToken, PlainBnfGeneratedDiagnosticsAppendExecution.tag])
    (by simp [variableToken])
    (by simp [env4, env3, env2, env1, env0, PlainBnfGeneratedScalarListSyntax.consEnv]) allDone]
  apply quote_exact
  simp [instantiate_atom, variableToken, PlainBnfGeneratedScalarListSyntax.result,
    PlainBnfGeneratedScalarListSyntax.tag, allDs]

/-- Sufficient depth for every finite scalar list. This is a model-depth
bound, not a native time or memory bound. -/
theorem run_complete (extra : Nat) (typed : Bool) (values : List Int) (origin : SExpr) :
    run (extra + 5 * (values.length + 1)) program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars values) origin) =
      .complete (answers values origin) := by
  match values with
  | [] =>
      simpa [PlainBnfGeneratedScalarListSyntax.scalars, answers] using
        PlainBnfGeneratedScalarListSyntax.run_nil (extra + 5) dataHeads typed origin
  | [scalar] => simpa [answers, diagnostics] using singleton_run extra typed scalar origin
  | first :: next :: rest =>
      have recursive := run_complete extra typed (next :: rest) origin
      have smallerDepth : extra + 5 * ((next :: rest).length + 1) =
          extra + 5 * rest.length + 3 + 7 := by simp only [List.length_cons]; omega
      rw [smallerDepth] at recursive
      simp only [answers, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at recursive
      have completed := cons_run (extra + 5 * rest.length + 3) typed first next
        (PlainBnfGeneratedScalarListSyntax.scalars rest) origin
        (diagnostics (next :: rest) origin) recursive
      have outerDepth : extra + 5 * ((first :: next :: rest).length + 1) =
          extra + 5 * rest.length + 3 + 12 := by simp only [List.length_cons]; omega
      rw [outerDepth]
      simpa only [PlainBnfGeneratedScalarListSyntax.scalars, answers, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, diagnostics] using completed
termination_by values.length

/-- All completed runs, including ones at smaller sufficient depths, have
exactly this ordered answer list. No extra answer or duplicate erasure is
licensed by forward preservation alone. -/
theorem completed_iff (typed : Bool) (values : List Int) (origin : SExpr)
    (observed : List SExpr) :
    (∃ depth, run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars values) origin) = .complete observed) ↔
      observed = answers values origin := by
  constructor
  · rintro ⟨depth, completed⟩
    exact GeneratedPeTTaDepthMonotonicity.run_completed_answers_unique depth
      (0 + 5 * (values.length + 1)) program dataHeads _ observed (answers values origin)
      completed (run_complete 0 typed values origin)
  · rintro rfl
    exact ⟨0 + 5 * (values.length + 1), run_complete 0 typed values origin⟩

theorem raw_typed_completed_same (values : List Int) (origin : SExpr) (observed : List SExpr) :
    (∃ depth, run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call false
        (PlainBnfGeneratedScalarListSyntax.scalars values) origin) = .complete observed) ↔
    (∃ depth, run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call true
        (PlainBnfGeneratedScalarListSyntax.scalars values) origin) = .complete observed) := by
  rw [completed_iff, completed_iff]

theorem completed_occurrence_count (depth : Nat) (typed : Bool)
    (values : List Int) (origin : SExpr) (observed : List SExpr)
    (completed : run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars values) origin) = .complete observed) :
    observed.length = if values.isEmpty then 0 else 1 := by
  rw [(completed_iff typed values origin observed).mp ⟨depth, completed⟩]
  simp only [answers]
  split <;> rfl

theorem diagnostics_empty_iff (values : List Int) (origin : SExpr) :
    diagnostics values origin = [] ↔
      values = [] ∨ PlainBnfLexicalScalarSemantics.ScalarListWellFormed values := by
  induction values with
  | nil => simp [diagnostics]
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases valid : isUnicodeScalarInt first <;>
            simp [diagnostics, unicodeDiagnostics, PlainBnfLexicalScalarSemantics.ScalarListWellFormed, valid]
      | cons next tail =>
          cases valid : isUnicodeScalarInt first <;> by_cases increasing : first < next <;>
            simp [diagnostics, unicodeDiagnostics, orderDiagnostics,
              PlainBnfLexicalScalarSemantics.ScalarListWellFormed, valid, increasing, ih]

private theorem encoded_diagnostics_empty_iff (values : List SExpr) :
    PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics values =
      PlainBnfGeneratedDiagnosticsAppendExecution.nil ↔ values = [] := by
  cases values <;> simp [PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics,
    PlainBnfGeneratedDiagnosticsAppendExecution.nil, PlainBnfGeneratedDiagnosticsAppendExecution.cons]

theorem successful_answer_iff (values : List Int) (origin : SExpr) :
    answers values origin = [PlainBnfGeneratedScalarListSyntax.result
      PlainBnfGeneratedDiagnosticsAppendExecution.nil] ↔
      PlainBnfLexicalScalarSemantics.ScalarListWellFormed values := by
  cases values with
  | nil => simp [answers, PlainBnfLexicalScalarSemantics.ScalarListWellFormed]
  | cons first rest =>
      simp [answers, PlainBnfGeneratedScalarListSyntax.result, encoded_diagnostics_empty_iff,
        diagnostics_empty_iff]

/-- The existing independent lexical semantics is precisely the domain
on which this generated caller returns a successful empty-diagnostic packet. -/
theorem completed_success_iff (typed : Bool) (values : List Int) (origin : SExpr) :
    (∃ depth, run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars values) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        PlainBnfGeneratedDiagnosticsAppendExecution.nil]) ↔
      PlainBnfLexicalScalarSemantics.ScalarListWellFormed values := by
  rw [completed_iff, eq_comm, successful_answer_iff]

theorem unicode_boundaries_control (typed : Bool) (origin : SExpr) :
    run 25 program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [0, 55295, 57344, 1114111]) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        PlainBnfGeneratedDiagnosticsAppendExecution.nil] := by
  have valid := PlainBnfLexicalScalarSemantics.checkScalarList_eq_true_iff
    [0, 55295, 57344, 1114111] |>.mp PlainBnfLexicalScalarSemantics.accepts_unicode_boundaries
  have completed := run_complete 0 typed [0, 55295, 57344, 1114111] origin
  change run 25 program dataHeads _ = _ at completed
  rw [(successful_answer_iff _ origin).mpr valid] at completed
  exact completed

theorem repeated_diagnostics_control (typed : Bool) (origin : SExpr) :
    run 20 program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [65, 65, 65]) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
          [.list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom "65", .atom "65", origin],
           .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom "65", .atom "65", origin]])] := by
  have repr65 : Int.repr 65 = "65" := by decide
  simpa [answers, diagnostics, unicodeDiagnostics, orderDiagnostics, isUnicodeScalarInt, repr65] using
    run_complete 0 typed [65, 65, 65] origin

/-- Repeated errors of different kinds expose reordering as well as
deduplication: Unicode, adjacency, then the tail's Unicode diagnostic. -/
theorem mixed_diagnostics_control (typed : Bool) (origin : SExpr) :
    run 15 program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [-1, -1]) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
          [.list [.atom "BNFInvalidUnicodeScalarV1", .atom "-1", origin],
           .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom "-1", .atom "-1", origin],
           .list [.atom "BNFInvalidUnicodeScalarV1", .atom "-1", origin]])] := by
  have reprMinus : Int.repr (-1) = "-1" := by decide
  simpa [answers, diagnostics, unicodeDiagnostics, orderDiagnostics, isUnicodeScalarInt, reprMinus] using
    run_complete 0 typed [-1, -1] origin

theorem repeated_diagnostics_not_collapsed (typed : Bool) (origin : SExpr) :
    run 20 program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [65, 65, 65]) origin) ≠
      .complete [PlainBnfGeneratedScalarListSyntax.result
        (PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics
          [.list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom "65", .atom "65", origin]])] := by
  rw [repeated_diagnostics_control]
  simp [PlainBnfGeneratedScalarListSyntax.result,
    PlainBnfGeneratedDiagnosticsAppendExecution.diagnostics,
    PlainBnfGeneratedDiagnosticsAppendExecution.cons, PlainBnfGeneratedDiagnosticsAppendExecution.nil]

theorem zero_depth_is_exhausted (typed : Bool) (scalar : Int) (origin : SExpr) :
    run 0 program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [scalar]) origin) = .exhausted := by
  rw [PlainBnfGeneratedScalarListSyntax.run_single]
  rfl

theorem empty_input_never_succeeds (typed : Bool) (origin : SExpr) :
    ¬ ∃ depth, run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed PlainBnfGeneratedScalarListSyntax.nil origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result PlainBnfGeneratedDiagnosticsAppendExecution.nil] := by
  simp [PlainBnfGeneratedScalarListSyntax.run_nil]

theorem surrogate_never_succeeds (typed : Bool) (origin : SExpr) :
    ¬ ∃ depth, run depth program dataHeads
      (PlainBnfGeneratedScalarListSyntax.call typed
        (PlainBnfGeneratedScalarListSyntax.scalars [55296]) origin) =
      .complete [PlainBnfGeneratedScalarListSyntax.result PlainBnfGeneratedDiagnosticsAppendExecution.nil] := by
  rw [completed_success_iff]
  simp [PlainBnfLexicalScalarSemantics.ScalarListWellFormed, isUnicodeScalarInt]

#print axioms run_complete
#print axioms order_wrapper_answers
#print axioms completed_iff
#print axioms raw_typed_completed_same
#print axioms completed_success_iff
#print axioms repeated_diagnostics_control
#print axioms mixed_diagnostics_control
#print axioms repeated_diagnostics_not_collapsed

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarListExecution
