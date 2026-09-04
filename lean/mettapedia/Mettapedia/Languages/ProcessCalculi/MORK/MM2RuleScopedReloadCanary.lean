import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# End-to-end rule-scoped reload controls

These controls parse and execute a complete self-reloading MM2 directive.  A
captured input/output pair republishes the loader, while a variable occurring
only inside a newly emitted rule remains a local binder.  Compact-key support
identity prevents an alpha-renamed copy of the loader from accumulating.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT
open ReflectiveComputable

private def loaderLocation : Atom :=
  .expression [.symbol "0", .symbol "rule-scoped-loader"]

private def loadTrigger : Atom :=
  .expression [.symbol "load-rule"]

private def loaderSelfPattern : Atom :=
  .expression [.symbol "exec", loaderLocation,
    .var "captured-input", .var "captured-output"]

private def emittedRuleLocation : Atom :=
  .expression [.symbol "1", .symbol "emitted-local-rule"]

private def emittedRule : Atom :=
  .expression [.symbol "exec", emittedRuleLocation,
    .expression [.symbol ",",
      .expression [.symbol "request", .var "item"]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "response", .var "item", .var "fresh"]]]]

private def loaderInputExpression : Atom :=
  .expression [.symbol ",", loaderSelfPattern, loadTrigger]

private def loaderOutputExpression : Atom :=
  .expression [.symbol "O",
    .expression [.symbol "+", loaderSelfPattern],
    .expression [.symbol "-", loadTrigger],
    .expression [.symbol "+", emittedRule]]

private def loaderAtom : Atom :=
  .expression [.symbol "exec", loaderLocation,
    loaderInputExpression, loaderOutputExpression]

private def loaderDirective : SourceExecFact :=
  { atom := loaderAtom
    loc := loaderLocation
    rule :=
      { priority := 0
        name := "rule-scoped-loader"
        input := .compat ⟨[loaderSelfPattern, loadTrigger]⟩
        guards := []
        tmpl := ⟨[.add loaderSelfPattern, .remove loadTrigger,
          .add emittedRule]⟩ } }

/-- The strict syntax-to-directive decoder reconstructs the authored loader;
the execution canary does not bypass parsing by trusting a hand-built rule. -/
theorem loaderAtom_decodes_exactly :
    extractSupportedSourceExecFact loaderAtom = some loaderDirective := by
  decide

/-- One firing republishes the loader, consumes its trigger, and installs the
rule containing an output-local binder. -/
theorem loaderDirective_fires_exactly :
    cFireRuleScopedSourceExecFact [loaderAtom, loadTrigger] loaderDirective =
      [loaderAtom, emittedRule] := by
  set_option maxRecDepth 10000 in
    decide

/-- Scheduling, parsing, matching, and sink execution form one exact GSLT
step for the complete loader fixture. -/
theorem loaderProgram_scheduled_step :
    (ruleScopedNativeListExecGSLT .leaveInert).Step
      [loaderAtom, loadTrigger] [loaderAtom, emittedRule] := by
  rw [ruleScopedNativeListExecGSLT_step_iff]
  set_option maxRecDepth 10000 in
    decide

/-- The older fully-bound output condition loses the emitted local rule.  This
separation is the regression control that makes the new semantics substantive. -/
theorem strictReflectiveExecution_loses_outputLocalRule :
    cFireReflectiveSourceExecFact [loaderAtom, loadTrigger] loaderDirective =
      [loaderAtom] := by
  decide

private def inheritedVariableInput : InputSpec :=
  .explicit [.neqConstraint (.var "inherited") (.var "witness")]

private def inheritedVariableDirective : SourceExecFact :=
  { atom := .expression [.symbol "exec",
      .expression [.symbol "0", .symbol "reject-unmatched"],
      .expression [.symbol "I",
        .expression [.symbol "!=", .var "inherited", .var "witness"]],
      .expression [.symbol "O",
        .expression [.symbol "+", .var "inherited"]]]
    loc := .expression [.symbol "0", .symbol "reject-unmatched"]
    rule :=
      { priority := 0
        name := "reject-unmatched"
        input := inheritedVariableInput
        guards := []
        tmpl := ⟨[.add (.var "inherited")]⟩ } }

/-- A matcher row that binds another variable cannot publish an unbound
variable inherited from the input. -/
theorem unmatchedInputVariable_cannot_escape :
    cFireRuleScopedSourceExecFact
      [inheritedVariableDirective.atom, .symbol "data"]
      inheritedVariableDirective = [.symbol "data"] := by
  decide

#print axioms loaderAtom_decodes_exactly
#print axioms loaderDirective_fires_exactly
#print axioms loaderProgram_scheduled_step
#print axioms strictReflectiveExecution_loses_outputLocalRule
#print axioms unmatchedInputVariable_cannot_escape

end Mettapedia.Languages.ProcessCalculi.MORK
