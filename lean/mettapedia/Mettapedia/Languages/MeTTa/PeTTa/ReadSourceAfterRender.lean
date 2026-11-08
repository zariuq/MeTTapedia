import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-! Read after render, for data. The source reader reads one rendered
expression, spelled as the renderer spells it and with nothing after it,
back as exactly that atom. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing

section Scanner

open SourceScanSegments (makeScanState initialScanState)
open private stepScan parserDialectOf finalizeCurr splitProgramForms from Algorithms.MeTTa.Simple.Parser
open private step_top_open step_top_close empty_trimmed from Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-- One rendered expression, with nothing after it, is one form. -/
theorem scan_form {items : List Atom} {parts : List (List Char)} {expressions : List SExpr}
    (children : RenderedList items parts expressions) (line : Nat) (forms : List (Nat × String)) :
    ('(' :: joinSpace parts ++ [')']).foldl SourceScanSegments.step ((between line).state [] forms) =
      (between line).state [] ((line, String.ofList ('(' :: joinSpace parts ++ [')'])) :: forms) := by
  have opened := SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _ (step_top_open line)
    (scan_items children line 1 line (by omega))
  have shape : '(' :: joinSpace parts ++ [')'] = (['('] ++ joinSpace parts) ++ [')'] := by simp
  rw [shape, List.foldl_append, opened [] forms]
  simp only [List.foldl_cons, List.foldl_nil, List.append_nil, List.reverse_cons, List.singleton_append]
  rw [show (joinSpace parts).reverse ++ ['('] = (joinSpace parts).reverse ++ ['('] from rfl, step_top_close]

/-- **The scanner reports one rendered expression as one form.** -/
theorem split_form {items : List Atom} {parts : List (List Char)} {expressions : List SExpr}
    (children : RenderedList items parts expressions) :
    splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta)
        (String.ofList ('(' :: joinSpace parts ++ [')'])) =
      .ok [(1, String.ofList ('(' :: joinSpace parts ++ [')']))] := by
  have scanned := scan_form children 1 []
  have initial : (between 1).state [] [] = SourceScanSegments.initialScanState := rfl
  rw [initial] at scanned
  have actual : ('(' :: joinSpace parts ++ [')']).foldl (stepScan (parserDialectOf MeTTailCore.MeTTaSyntax.petta))
      SourceScanSegments.initialScanState =
      (between 1).state [] [(1, String.ofList ('(' :: joinSpace parts ++ [')']))] := scanned
  unfold splitProgramForms
  rw [String.toList_ofList]
  simp only [SourceScanSegments.initialScanState, makeScanState] at actual
  rw [actual]
  simp [between, SourceAccumulatorScan.Point.state, makeScanState, finalizeCurr, empty_trimmed]

end Scanner

section Source

open private parserDialectOf splitProgramForms from Algorithms.MeTTa.Simple.Parser

/-- The program parser reads one rendered expression as one expression. -/
theorem parse_rendered {items : List Atom} {parts : List (List Char)} {expressions : List SExpr}
    (children : RenderedList items parts expressions) :
    Algorithms.MeTTa.Simple.Parser.parseSExprProgramWithDetailed MeTTailCore.MeTTaSyntax.petta
        (String.ofList ('(' :: joinSpace parts ++ [')'])) = .ok [(1, .list expressions)] := by
  unfold Algorithms.MeTTa.Simple.Parser.parseSExprProgramWithDetailed
  dsimp only
  rw [split_form children]
  simp only [bind, Except.bind, List.mapM_cons, List.mapM_nil, parse_form children]
  rfl

/-- **Read after render, for one datum.** The source reader reads a rendered
expression back as exactly that atom. -/
theorem readSource_render {atom : Atom} {text : String} (rendered : render? atom = some text)
    (expression : ∃ items, atom = .expression items) :
    SpaceSemantics.readSource text = .ok [atom] := by
  obtain ⟨items, rfl⟩ := expression
  unfold render? at rendered
  cases chars : chars? (Atom.expression items) with
  | none => rw [chars] at rendered; cases rendered
  | some characters =>
    rw [chars] at rendered
    cases rendered
    obtain ⟨sexpr, source⟩ := rendered_of_chars chars
    cases source with
    | @expression _ parts expressions children =>
      unfold SpaceSemantics.readSource
      rw [parse_rendered children]
      simp only [Except.mapError, bind, Except.bind, List.map_cons, List.map_nil]
      exact read_expressions (.cons (.expression children) .nil)

end Source

#print axioms readSource_render

end Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
