import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.StagedBinding
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Reflective MM2 observations for typed graph decoding

MM2 reflection does not require a decoder-wide feature switch.  The authored
MM2 template semantics already distinguishes an unresolved outer variable
from a bound value whose internal variable bytes belong to a later execution
stage.  This module maps the latter case to the generic `opaqueCapture`
observation and proves that it cannot create outer-scope obligations.

The bridge is deliberately one-way: successful MM2 instantiation supplies an
opaque semantic value.  It does not recursively reinterpret the captured
payload as outer syntax.  A genuinely unbound outer template still fails
before any observation is emitted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ReflectiveMM2Bridge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.StagedBinding

/-- Instantiate one MM2 template and, on success, expose the resulting value
to the outer binding machine as an opaque value at the declared stage. -/
def observeInstantiated? (stage : Nat) (substitution : Subst)
    (template : Atom) (state : State String) : Option (State String) :=
  match instantiateTemplateAtom? substitution template with
  | none => none
  | some payload => some (State.observe state (.opaqueCapture stage payload))

/-- Every successful reflective instantiation preserves the complete outer
binding state.  Opaqueness is therefore a semantic event, not a mode toggle. -/
theorem observeInstantiated?_eq_some_of_instantiates
    (stage : Nat) (substitution : Subst) (template payload : Atom)
    (state : State String)
    (instantiates : instantiateTemplateAtom? substitution template =
      some payload) :
    observeInstantiated? stage substitution template state = some state := by
  simp [observeInstantiated?, instantiates]

/-! ## Concrete reflective and unbound controls -/

def capturedPattern : Atom :=
  .expression
    [.symbol ",", .expression [.symbol "task", .var "inner"]]

def capturedTemplate : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "done", .var "inner"]]]

def captureSubstitution : Subst :=
  [("patterns", capturedPattern), ("templates", capturedTemplate)]

def stagedExecTemplate : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "1", .symbol "next"],
      .var "patterns", .var "templates"]

def instantiatedExec : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "1", .symbol "next"],
      capturedPattern, capturedTemplate]

/-- The actual MM2 outer-template judgment accepts the reflective fixture. -/
theorem stagedExecTemplate_covered :
    templateCovered captureSubstitution stagedExecTemplate = true := by
  decide +kernel

/-- Successful instantiation retains the inner variable bytes. -/
theorem stagedExecTemplate_instantiates :
    instantiateTemplateAtom? captureSubstitution stagedExecTemplate =
      some instantiatedExec := by
  decide +kernel

/-- The same successfully instantiated MM2 value adds no outer binding or
use obligation when compiled to an opaque semantic observation. -/
theorem stagedExecTemplate_preserves_outer_binding_state
    (stage : Nat) (state : State String) :
    observeInstantiated? stage captureSubstitution stagedExecTemplate state =
      some state :=
  observeInstantiated?_eq_some_of_instantiates stage captureSubstitution
    stagedExecTemplate instantiatedExec state stagedExecTemplate_instantiates

def genuinelyUnboundTemplate : Atom :=
  .expression [.symbol "exec", .var "missing"]

/-- A missing outer binding is rejected by MM2 rather than mislabeled as an
opaque capture. -/
theorem genuinelyUnboundTemplate_rejected :
    instantiateTemplateAtom? ([] : Subst) genuinelyUnboundTemplate = none := by
  decide +kernel

/-- The bridge emits no semantic observation after outer-template failure. -/
theorem genuinelyUnboundTemplate_emits_nothing
    (stage : Nat) (state : State String) :
    observeInstantiated? stage ([] : Subst) genuinelyUnboundTemplate state =
      none := by
  simp [observeInstantiated?, genuinelyUnboundTemplate_rejected]

/-- If the same spelling is used as an ordinary outer variable, the generic
binding observer records the unresolved obligation.  This is the negative
control separating use from opaque capture. -/
theorem ordinary_outer_use_remains_pending :
    (0, "missing") ∈
      (State.observe (Payload := Atom) State.empty
        (.use 0 "missing")).pending := by
  apply State.observe_unbound_use_mem_pending
  simp [State.empty]

#print axioms observeInstantiated?_eq_some_of_instantiates
#print axioms stagedExecTemplate_covered
#print axioms stagedExecTemplate_instantiates
#print axioms stagedExecTemplate_preserves_outer_binding_state
#print axioms genuinelyUnboundTemplate_rejected
#print axioms genuinelyUnboundTemplate_emits_nothing
#print axioms ordinary_outer_use_remains_pending

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ReflectiveMM2Bridge
