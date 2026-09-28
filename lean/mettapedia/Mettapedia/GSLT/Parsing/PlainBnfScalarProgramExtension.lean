import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarCallerExecution

/-!
# Selected scalar execution under unrelated equation extensions

Only the actual raw/admitted scalar equations, their two Integer providers, and
the result tag are protected here. Other literal-headed equations may change
the program's behavior without changing this call. The condition concerns
ordered source occurrences, not hashes or equality of distinct answer sets.

This uses the existing finite ground execution model. It does not certify an
importer, native call leases, dynamic translator registrations, or a mutable
session snapshot. In particular, target translation must separately preserve
the stated interpretation of result patterns as inert data.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfScalarProgramExtension

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaTemplateInstantiation
open PlainBnfGeneratedScalarOrderSyntax
open PlainBnfGeneratedScalarOrderExecution
open PlainBnfGeneratedScalarCallerExecution

def consultedHeads : List String :=
  [symbol false, symbol true,
   GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex 0),
   GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex 1), tag]

structure Apart (additional : List (Nat × SExpr)) : Prop where
  literal : ∀ entry ∈ additional, LiteralEquationHead entry.2
  absent : ∀ name ∈ consultedHeads, equationsFor name additional = []

theorem scalar_consulted (typed : Bool) : symbol typed ∈ consultedHeads := by
  cases typed <;> simp [consultedHeads]

theorem provider_consulted (i : Fin 2) :
    GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex i) ∈ consultedHeads := by
  fin_cases i <;> simp [consultedHeads]

theorem tag_consulted : tag ∈ consultedHeads := by simp [consultedHeads]

theorem inventory_append (additional : List (Nat × SExpr)) (apart : Apart additional) :
    ScalarInventory (program ++ additional) where
  literal entry member := by
    rcases List.mem_append.mp member with original | added
    · exact literal_heads entry original
    · exact apart.literal entry added
  scalarRows typed := by
    simp only [equationsFor, List.filter_append]
    change equationsFor (symbol typed) program ++ equationsFor (symbol typed) additional = _
    rw [equationsFor_rows, apart.absent _ (scalar_consulted typed), List.append_nil]
  integerRows i := by
    simp only [equationsFor, List.filter_append]
    change equationsFor _ program ++ equationsFor _ additional = _
    rw [provider_rows, apart.absent _ (provider_consulted i), List.append_nil]
    rfl

theorem result_tag_append (additional : List (Nat × SExpr)) (apart : Apart additional) :
    equationsFor tag (program ++ additional) = [] := by
  simp only [equationsFor, List.filter_append]
  change equationsFor tag program ++ equationsFor tag additional = []
  rw [result_tag_not_callable, apart.absent _ tag_consulted]
  rfl

theorem worker_append_exact (additional : List (Nat × SExpr)) (apart : Apart additional)
    (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr) :
    run (depth + 4) (program ++ additional) dataHeads (call typed left right origin) =
      .complete [answer left right origin] :=
  run_exact_in _ (inventory_append additional apart) depth typed left right origin

theorem worker_append_no_invention (additional : List (Nat × SExpr)) (apart : Apart additional)
    (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr) (answers : List SExpr) :
    run (depth + 4) (program ++ additional) dataHeads (call typed left right origin) =
      .complete answers ↔ answers = [answer left right origin] := by
  simp [worker_append_exact additional apart, eq_comm]

/-- Both actual caller contexts run in the extended program. A common
continuation may itself use newly added definitions; it is not erased. -/
theorem caller_append_same (additional : List (Nat × SExpr)) (apart : Apart additional)
    (depth : Nat) (env : Bindings) (left right : Int) (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) (program ++ additional) dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) (program ++ additional) dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) :=
  actual_let_same_continuation_in _ (inventory_append additional apart)
    (result_tag_append additional apart) depth env left right origin continuation
    first second location

def observerRow : Nat × SExpr :=
  (1, .list [.atom "=", .list [.atom "bnf-extension-observer-v1"],
    .list [.atom "quote", .atom "new-observation"]])

theorem observer_apart : Apart [observerRow] where
  literal entry member := by
    have same : entry = observerRow := by simpa using member
    subst entry
    intro head body parsed
    simp only [observerRow, equation?, Option.some.injEq, Prod.mk.injEq] at parsed
    rcases parsed with ⟨rfl, rfl⟩
    exact ⟨"bnf-extension-observer-v1", [], rfl, by
      simp [GeneratedPeTTaResultBinding.variableToken]⟩
  absent name member := by
    have less : GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex 0) =
        "gslt:ground-integer-less" := rfl
    have notLess : GeneratedPeTTaIntegerProviderDispatch.symbol (providerIndex 1) =
        "gslt:ground-integer-not-less" := rfl
    simp only [consultedHeads, less, notLess, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [equationsFor, observerRow, equationSymbol?, equation?, symbol, tag]

/-- The permitted extension is not inert as a whole program: its new
function executes and produces an observation of its own. -/
theorem observer_executes :
    run 1 [observerRow] [] (.list [.atom "bnf-extension-observer-v1"]) =
      .complete [.atom "new-observation"] := by
  simp [run, runWith, reserved, knownFunction, hasArity, equationsFor,
    observerRow, equationSymbol?, equation?, dispatch, matchEquation,
    GeneratedPeTTaResultBinding.bindResult, GeneratedPeTTaResultBinding.template,
    GeneratedPeTTaResultBinding.templates, GeneratedPeTTaResultBinding.variableToken,
    SourceSExprPatternCodec.encode, SourceSExprPatternCodec.encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, collect, eval, instantiate_atom]

theorem observer_executes_in_extended_program :
    run 1 (program ++ [observerRow]) [] (.list [.atom "bnf-extension-observer-v1"]) =
      .complete [.atom "new-observation"] := by
  have absent : equationsFor "bnf-extension-observer-v1" program = [] := by
    rw [equationsFor_program]
    rfl
  have selected : equationsFor "bnf-extension-observer-v1" (program ++ [observerRow]) =
      [observerRow] := by
    simp only [equationsFor, List.filter_append]
    change equationsFor "bnf-extension-observer-v1" program ++
      equationsFor "bnf-extension-observer-v1" [observerRow] = _
    rw [absent]
    simp [equationsFor, observerRow, equationSymbol?, equation?]
  have matched : dispatch [] (.list [.atom "bnf-extension-observer-v1"])
      (program ++ [observerRow]) = [(observerRow, [])] := by
    rw [dispatch_literal_filter [] _ [] _ (inventory_append _ observer_apart).literal, selected]
    simp [dispatch, observerRow, matchEquation, equation?, GeneratedPeTTaResultBinding.bindResult,
      GeneratedPeTTaResultBinding.template, GeneratedPeTTaResultBinding.templates,
      GeneratedPeTTaResultBinding.variableToken, SourceSExprPatternCodec.encode,
      SourceSExprPatternCodec.encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  rw [call_single_match 1 (program ++ [observerRow]) [] "bnf-extension-observer-v1" []
    observerRow [] (.list [.atom "bnf-extension-observer-v1"])
    (.list [.atom "quote", .atom "new-observation"])
    (by simp [reserved]) (by simp [knownFunction, selected])
    (by rw [hasArity, selected]; rfl) matched (by rfl)]
  simp [eval, instantiate_atom, GeneratedPeTTaResultBinding.variableToken]

theorem duplicate_scalar_not_apart (typed : Bool) (i : Fin 2) :
    ¬ Apart [row typed i] := by
  intro apart
  have absent := apart.absent _ (scalar_consulted typed)
  simp [equationsFor, equationSymbol?, row_equation, head_shape] at absent

theorem duplicate_provider_not_apart (i : Fin 2) :
    ¬ Apart [(823 + 2 * i.val, (GeneratedPeTTaIntegerProviderDispatch.row (providerIndex i)).2)] := by
  intro apart
  have absent := apart.absent _ (provider_consulted i)
  simp [equationsFor, equationSymbol?, GeneratedPeTTaIntegerProviderDispatch.row_equation,
    GeneratedPeTTaIntegerProviderDispatch.head_shape] at absent

def callableTagRow : Nat × SExpr :=
  (2, .list [.atom "=", .list [.atom tag, .atom "$x"], .atom "collapse"])

theorem callable_tag_not_apart : ¬ Apart [callableTagRow] := by
  intro apart
  have absent := apart.absent _ tag_consulted
  simp [equationsFor, equationSymbol?, equation?, callableTagRow] at absent

theorem callable_tag_invalidates_inert_schema (typed : Bool) :
    inertBinder (program ++ [callableTagRow]) dataHeads (callerSchema typed) = false := by
  rw [caller_schema]
  simp [inertBinder, knownFunction, equationsFor, callableTagRow, equationSymbol?, equation?]

#print axioms inventory_append
#print axioms worker_append_no_invention
#print axioms caller_append_same
#print axioms observer_apart
#print axioms observer_executes_in_extended_program
#print axioms callable_tag_invalidates_inert_schema

end Mettapedia.GSLT.Parsing.PlainBnfScalarProgramExtension
