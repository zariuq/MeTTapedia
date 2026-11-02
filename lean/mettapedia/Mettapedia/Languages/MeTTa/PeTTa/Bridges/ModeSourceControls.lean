import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeReadoutSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceReplay
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
import Mettapedia.Util.CbvStringLiteral

/-! Source-text, schema, tie, scope, effect and multiplicity controls for the
captured CDLP mode adapter. The program is loaded by the existing PeTTa reader.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceControls

attribute [local cbv_simproc cbv_eval] Mettapedia.Util.CbvStringLiteral.stringDecision
attribute [local cbv_opaque] String.decEq

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ModeAggregation
open Eval SpaceSemantics MeTTaIL.WireKit ModeFoldSource

def sourceText : String :=
  "(= (mode-step ($c $cn $b $bn) $x)\n   (if (== $x $c) ($c (+ $cn 1) $b $bn)\n       (if (> $cn $bn) ($x 1 $c $cn) ($x 1 $b $bn))))\n(= (mode $sorted)\n   (let ($c $cn $b $bn) (foldl-atom $sorted (none 0 none 0) $acc $x (mode-step $acc $x))\n     (if (> $cn $bn) $c $b)))"

def names : Names := ⟨"c", "cn", "b", "bn", "x"⟩

def stepBody (n : Names) : Atom :=
  apply "if" [apply "==" [.var n.item, .var n.current],
    .expression [.var n.current, apply "+" [.var n.count, number 1], .var n.best, .var n.bestCount],
    apply "if" [apply ">" [.var n.count, .var n.bestCount],
      .expression [.var n.item, number 1, .var n.current, .var n.count],
      .expression [.var n.item, number 1, .var n.best, .var n.bestCount]]]

def finishBody (n : Names) : Atom := apply "if" [apply ">" [.var n.count, .var n.bestCount], .var n.current, .var n.best]

def stepEquation : Equation := ⟨"mode-step", arguments names, stepBody names⟩
def modeEquation : Equation :=
    ⟨"mode", [.var "sorted"], apply "let" [ModeReadoutSource.pattern names,
      apply "foldl-atom" [.var "sorted", encode SortedRun.initial, .var "acc", .var "x",
        apply "mode-step" [.var "acc", .var "x"]], finishBody names]⟩
def program : Program := {
  equations := [stepEquation, modeEquation]
  declarations := [], layout := [.equation, .equation] }

private theorem renderedZero : ReadAfterRender.Rendered (.grounded (.int 0)) ['0'] (.atom "0") := by
  simpa [ReadAfterRender.intChars, ReadAfterRender.decimal, ReadAfterRender.digitChar] using
    ReadAfterRender.Rendered.int 0

private theorem renderedOne : ReadAfterRender.Rendered (.grounded (.int 1)) ['1'] (.atom "1") := by
  simpa [ReadAfterRender.intChars, ReadAfterRender.decimal, ReadAfterRender.digitChar] using
    ReadAfterRender.Rendered.int 1

theorem step_read : readExpression ModeSourceReplay.form1Syntax = .ok stepEquation.toAtom := by
  apply ReadAfterRender.read_expression
  dsimp only [ModeSourceReplay.form1Syntax, stepEquation, Equation.toAtom, arguments, Names.fields,
    names, stepBody, apply, number, encoded, MeTTaIL.CettaWireAtom.encode]
  repeat first
    | apply ReadAfterRender.Rendered.expression
    | apply ReadAfterRender.RenderedList.cons
    | exact ReadAfterRender.RenderedList.nil
    | apply ReadAfterRender.Rendered.symbol
    | apply ReadAfterRender.Rendered.var
    | exact renderedZero
    | exact renderedOne
    | apply ReadAfterRender.Rendered.int
    | decide_cbv

theorem mode_read : readExpression ModeSourceReplay.form2Syntax = .ok modeEquation.toAtom := by
  apply ReadAfterRender.read_expression
  dsimp only [ModeSourceReplay.form2Syntax, modeEquation, Equation.toAtom, ModeReadoutSource.pattern,
    Names.fields, names, finishBody, apply, encode, SortedRun.initial, labelAtom, labelData,
    ScalarSource.encode, number, encoded, MeTTaIL.CettaWireAtom.encode]
  repeat first
    | apply ReadAfterRender.Rendered.expression
    | apply ReadAfterRender.RenderedList.cons
    | exact ReadAfterRender.RenderedList.nil
    | apply ReadAfterRender.Rendered.symbol
    | apply ReadAfterRender.Rendered.var
    | exact renderedZero
    | exact renderedOne
    | apply ReadAfterRender.Rendered.int
    | decide_cbv

theorem source_program_exact : readProgram sourceText = .ok program := by
  change readProgram ModeSourceReplay.sourceText = .ok program
  unfold readProgram
  rw [ModeSourceReplay.commands_exact]
  simp only [Except.mapError, bind, Except.bind, List.mapM_cons, List.mapM_nil, step_read, mode_read]
  rfl
theorem source_is_loaded : (readProgram sourceText).isOk = true := by rw [source_program_exact]; rfl
theorem actual_callback_is_recognized : (ModeFoldSource.infer program "mode-step").isSome = true := by decide +kernel

def step : ModeFoldSource.Certified program "mode-step" :=
  (ModeFoldSource.infer program "mode-step").get actual_callback_is_recognized

theorem source_names_preserved : step.names = names := by decide +kernel
theorem actual_readout_is_recognized :
    (ModeReadoutSource.infer program step.names (finishBody names)).isSome = true := by decide +kernel

def finish : ModeReadoutSource.Certified program step.names (finishBody names) :=
  (ModeReadoutSource.infer program step.names (finishBody names)).get actual_readout_is_recognized

theorem arbitrary_natural_votes_have_source_histogram_meaning (world : Effects.State)
    (labels : List Nat) (answer : Atom) :
    ModeReadoutSource.Completes program "mode-step" step.names (finishBody names) world
      (labels.mergeSort (· ≤ ·)) answer ↔ answer = labelAtom (sparseReadout (sparseHistogram labels)) :=
  ModeReadoutSource.permuted_then_sorted_source step finish world labels answer

theorem smallest_tie_is_retained (world : Effects.State) :
    ModeReadoutSource.Completes program "mode-step" step.names (finishBody names) world [1, 1, 2, 2] (number 1) :=
  ModeReadoutSource.source_complete step finish world [1, 1, 2, 2]

theorem duplicate_votes_change_the_source_result (world : Effects.State) :
    ModeReadoutSource.Completes program "mode-step" step.names (finishBody names) world [1, 2, 2] (number 2) ∧
    ModeReadoutSource.Completes program "mode-step" step.names (finishBody names) world [1, 2] (number 1) :=
  ⟨ModeReadoutSource.source_complete step finish world [1, 2, 2],
    ModeReadoutSource.source_complete step finish world [1, 2]⟩

theorem empty_mode_returns_the_sentinel_not_no_answer (world : Effects.State) :
    ModeReadoutSource.Completes program "mode-step" step.names (finishBody names) world [] (.symbol "none") :=
  ModeReadoutSource.source_complete step finish world []

def renamed : Names := ⟨"previous", "run-size", "winner", "max-size", "incoming"⟩
def renamedProgram : Program := {equations := [⟨"renamed-fold", arguments renamed, stepBody renamed⟩], declarations := []}

theorem function_and_formal_names_are_not_the_schema :
    (ModeFoldSource.infer renamedProgram "renamed-fold").isSome = true := by decide +kernel

def wrappedProgram : Program :=
  {equations := [⟨"wrapped", arguments names,
    apply "if" [Effects.boolean true, stepBody names, stepBody names]⟩], declarations := []}

theorem pure_constant_choice_wrapper_is_recognized :
    (ModeFoldSource.infer wrappedProgram "wrapped").isSome = true := by decide +kernel

def reversedFinish : Atom := apply "if" [apply "<" [.var names.bestCount, .var names.count], .var names.current, .var names.best]

theorem reversed_order_test_has_the_same_readout_schema :
    (ModeReadoutSource.infer program names reversedFinish).isSome = true := by decide +kernel

def nonstrictFinish : Atom := apply "if" [apply ">=" [.var names.count, .var names.bestCount], .var names.current, .var names.best]

theorem changing_the_tie_rule_is_rejected :
    (ModeReadoutSource.infer program names nonstrictFinish).isNone = true := by decide +kernel

def duplicateProgram : Program :=
  {equations := [⟨"dup", arguments names, stepBody names⟩, ⟨"dup", arguments names, stepBody names⟩], declarations := []}

theorem overlapping_equations_are_not_one_answer : (ModeFoldSource.infer duplicateProgram "dup").isNone = true := by decide +kernel

def aliased : Names := ⟨"same", "n", "best", "bn", "same"⟩
def aliasedProgram : Program := {equations := [⟨"aliased", arguments aliased, stepBody aliased⟩], declarations := []}

theorem aliasing_an_input_and_accumulator_field_is_rejected :
    (ModeFoldSource.infer aliasedProgram "aliased").isNone = true := by decide +kernel

def effectProgram : Program :=
  {equations := [⟨"effect", arguments names,
    apply "if" [Effects.boolean true, stepBody names, apply "println!" [.var names.item]]⟩], declarations := []}

theorem normalization_does_not_hide_an_unextracted_effect :
    (ModeFoldSource.infer effectProgram "effect").isNone = true := by decide +kernel

theorem unsorted_source_is_not_a_histogram (world : Effects.State) :
    ModeReadoutSource.Completes program "mode-step" step.names (finishBody names) world [1, 2, 2, 1, 1] (number 2) ∧
      mode [1, 2, 2, 1, 1] = some 1 :=
  ⟨ModeReadoutSource.source_complete step finish world [1, 2, 2, 1, 1], by decide⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceControls
