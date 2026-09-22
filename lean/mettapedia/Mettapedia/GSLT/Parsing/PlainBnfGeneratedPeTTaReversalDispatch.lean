import Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaDispatch

/-!
# Actual generated reversal equation dispatch

The two equations are retrieved from the generated component fixture. Checked
shape observations expose their existing heads and bodies; no replacement
equations or body evaluator are introduced.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaReversalDispatch

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult)
open GeneratedPeTTaEquationDispatch
open PlainBnfGeneratedPeTTaSyntax (generatedProgram generatedWorkers generated_worker_count)

def worker : String :=
  PlainBnfGeneratedPeTTaSyntax.workerName "BNFDiscoveryReverseDefinitionsV1" 2 1

def call (reversed accumulator : SExpr) : SExpr :=
  .list [.atom worker, reversed, accumulator]

def nilRow : Nat × SExpr :=
  generatedWorkers[14]'(by rw [generated_worker_count]; decide)

def consRow : Nat × SExpr :=
  generatedWorkers[15]'(by rw [generated_worker_count]; decide)

/-- All four projections come from the retrieved actual equations. -/
def nilHead : SExpr := ((equation? nilRow.2).get (by rfl)).1
def nilBody : SExpr := ((equation? nilRow.2).get (by rfl)).2
def consHead : SExpr := ((equation? consRow.2).get (by rfl)).1
def consBody : SExpr := ((equation? consRow.2).get (by rfl)).2

def nilBindings (accumulator : SExpr) : Bindings := [("$result", encode accumulator)]

def consBindings (head tail accumulator : SExpr) : Bindings :=
  [("$before", encode accumulator), ("$head", encode head), ("$tail", encode tail)]

theorem nil_row_line : nilRow.1 = 798 := rfl
theorem cons_row_line : consRow.1 = 802 := rfl

theorem nil_equation : equation? nilRow.2 = some (nilHead, nilBody) := rfl
theorem cons_equation : equation? consRow.2 = some (consHead, consBody) := rfl

/-- Checked shape observations; the definitions above retrieve original data. -/
theorem nil_head_shape :
    nilHead = .list [.atom worker, .atom "BNFDefinitionsNilV1", .atom "$result"] := rfl

theorem cons_head_shape :
    consHead = .list [.atom worker,
      .list [.atom "BNFDefinitionsConsV1", .atom "$head", .atom "$tail"], .atom "$before"] := rfl

theorem nil_body_shape :
    nilBody = .list [.atom "quote",
      .list [.atom "gslt:result:BNFDiscoveryReverseDefinitionsV1:110", .atom "$result"]] := rfl

theorem cons_body_shape :
    consBody = .list [.atom "let",
      .list [.atom "gslt:result:BNFDiscoveryReverseDefinitionsV1:110", .atom "$after"],
      call (.atom "$tail") (.list [.atom "BNFDefinitionsConsV1", .atom "$head", .atom "$before"]),
      .list [.atom "quote",
        .list [.atom "gslt:result:BNFDiscoveryReverseDefinitionsV1:110", .atom "$after"]]] := rfl

theorem reversal_rows_exact : equationsFor worker generatedWorkers = [nilRow, consRow] := rfl

theorem whole_reversal_rows : equationsFor worker generatedProgram = [nilRow, consRow] := by
  have rows := PlainBnfGeneratedPeTTaDispatch.equationsFor_worker_filter
    "BNFDiscoveryReverseDefinitionsV1" 2 1 generatedProgram
  change equationsFor worker generatedWorkers = equationsFor worker generatedProgram at rows
  exact rows.symm.trans reversal_rows_exact

theorem dispatch_reversal_rows (reversed accumulator : SExpr) :
    dispatch [] (call reversed accumulator) generatedProgram =
      dispatch [] (call reversed accumulator) [nilRow, consRow] := by
  have whole := PlainBnfGeneratedPeTTaDispatch.generated_worker_dispatch []
    "BNFDiscoveryReverseDefinitionsV1" 2 1 [reversed, accumulator]
  change dispatch [] (call reversed accumulator) generatedProgram =
    dispatch [] (call reversed accumulator) (equationsFor worker generatedWorkers) at whole
  exact whole.trans (congrArg (dispatch [] (call reversed accumulator)) reversal_rows_exact)

theorem match_nil (accumulator : SExpr) :
    matchEquation [] (call (.atom "BNFDefinitionsNilV1") accumulator) nilRow.2 =
      [nilBindings accumulator] := by
  simp [matchEquation, nil_equation, bindResult, nil_head_shape, call, worker,
    PlainBnfGeneratedPeTTaSyntax.workerName, PlainBnfGeneratedPeTTaSyntax.modeBits,
    template, templates, variableToken, encode, encodeList, matchPattern, matchArgs,
    mergeBindings, List.foldlM, nilBindings]

theorem cons_does_not_match_nil (accumulator : SExpr) :
    matchEquation [] (call (.atom "BNFDefinitionsNilV1") accumulator) consRow.2 = [] := by
  simp [matchEquation, cons_equation, bindResult, cons_head_shape, call, worker,
    PlainBnfGeneratedPeTTaSyntax.workerName, PlainBnfGeneratedPeTTaSyntax.modeBits,
    template, templates, variableToken, encode, encodeList, matchPattern, matchArgs]

theorem match_cons (head tail accumulator : SExpr) :
    matchEquation [] (call (.list [.atom "BNFDefinitionsConsV1", head, tail]) accumulator) consRow.2 =
      [consBindings head tail accumulator] := by
  simp [matchEquation, cons_equation, bindResult, cons_head_shape, call, worker,
    PlainBnfGeneratedPeTTaSyntax.workerName, PlainBnfGeneratedPeTTaSyntax.modeBits,
    template, templates, variableToken, encode, encodeList, matchPattern, matchArgs,
    mergeBindings, List.foldlM, consBindings]

theorem nil_does_not_match_cons (head tail accumulator : SExpr) :
    matchEquation [] (call (.list [.atom "BNFDefinitionsConsV1", head, tail]) accumulator) nilRow.2 = [] := by
  simp [matchEquation, nil_equation, bindResult, nil_head_shape, call, worker,
    PlainBnfGeneratedPeTTaSyntax.workerName, PlainBnfGeneratedPeTTaSyntax.modeBits,
    template, templates, variableToken, encode, encodeList, matchPattern, matchArgs]

/-- Fresh-call dispatch against every equation in the actual generated fixture. -/
theorem dispatch_nil (accumulator : SExpr) :
    dispatch [] (call (.atom "BNFDefinitionsNilV1") accumulator) generatedProgram =
      [(nilRow, nilBindings accumulator)] := by
  rw [dispatch_reversal_rows]
  simp [dispatch, match_nil, cons_does_not_match_nil]

theorem dispatch_cons (head tail accumulator : SExpr) :
    dispatch [] (call (.list [.atom "BNFDefinitionsConsV1", head, tail]) accumulator) generatedProgram =
      [(consRow, consBindings head tail accumulator)] := by
  rw [dispatch_reversal_rows]
  simp [dispatch, match_cons, nil_does_not_match_cons]

/-- A nullary list is not the literal atom used by the nil equation. -/
theorem dispatch_nullary_nil (accumulator : SExpr) :
    dispatch [] (call (.list [.atom "BNFDefinitionsNilV1"]) accumulator) generatedProgram = [] := by
  rw [dispatch_reversal_rows]
  simp [dispatch, matchEquation, nil_equation, cons_equation, bindResult,
    nil_head_shape, cons_head_shape, call, worker,
    PlainBnfGeneratedPeTTaSyntax.workerName, PlainBnfGeneratedPeTTaSyntax.modeBits,
    template, templates, variableToken, encode, encodeList, matchPattern, matchArgs]

theorem missing_nil_equation_has_no_match (accumulator : SExpr) :
    dispatch [] (call (.atom "BNFDefinitionsNilV1") accumulator) [consRow] = [] := by
  simp [dispatch, cons_does_not_match_nil]

/-- Adding another occurrence of the actual nil equation adds another answer. -/
theorem duplicate_nil_equation_has_two_matches (accumulator : SExpr) :
    dispatch [] (call (.atom "BNFDefinitionsNilV1") accumulator) (generatedProgram ++ [nilRow]) =
      [(nilRow, nilBindings accumulator), (nilRow, nilBindings accumulator)] := by
  rw [dispatch_append, dispatch_nil]
  simp [dispatch, match_nil]

theorem duplicate_nil_equation_does_not_license_once (accumulator : SExpr) :
    let answers := dispatch [] (call (.atom "BNFDefinitionsNilV1") accumulator)
      (generatedProgram ++ [nilRow])
    answers ≠ answers.take 1 := by
  dsimp only
  rw [duplicate_nil_equation_has_two_matches]
  simp

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaReversalDispatch
