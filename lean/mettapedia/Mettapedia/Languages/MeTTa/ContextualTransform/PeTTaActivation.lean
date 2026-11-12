import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContexts

/-!
# Written calls and held syntax inside actual PeTTa contexts

The source registry, installed private code and built-in interface determine written-call admission.
Saved caller frames do not change that classification. Quotation and variables
that already hold values use different source rules: a callable-looking value
does not become code merely because its syntax names a function.

The controls also distinguish a logically bound variable from a lexical binder:
an enclosing continuation can observe a binding unused by the immediate body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaActivation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying PeTTaContexts

/-- A registry's classification predicate. The current source rule uses the
registry combined with the configuration's installed private code. -/
def callable (registry : SpaceSemantics.Program) (head : String) : Bool :=
  Eval.ioHead head || StdLib.known head || registry.equations.any (·.head == head)

theorem callable_with_privateCode (registry : SpaceSemantics.Program)
    (code : List SpaceSemantics.Equation) (head : String) (known : callable registry head = true) :
    callable (codeRegistry registry code) head = true := by
  have alternatives : (Eval.ioHead head || StdLib.known head) = true ∨
      registry.equations.any (·.head == head) = true := by
    simpa only [callable,Bool.or_eq_true] using known
  rcases alternatives with builtin | authored
  · simp [callable,codeRegistry,List.any_append,builtin]
  · simp [callable,codeRegistry,List.any_append,authored]

theorem current_written_call_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (arguments : List Atom)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : callable (codeRegistry registry base.privateCode) head = true) :
    step registry (atExpression base bindings (.expression (.symbol head :: arguments))) =
      some { base with control := .arguments bindings (.function head) arguments [] 0 } :=
  transition_step (.call_enter rfl ordinary recognized)

theorem written_call_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (arguments : List Atom)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : callable registry head = true) :
    step registry (atExpression base bindings (.expression (.symbol head :: arguments))) =
      some { base with control := .arguments bindings (.function head) arguments [] 0 } := by
  exact current_written_call_step registry base bindings head arguments ordinary
    (callable_with_privateCode registry base.privateCode head recognized)

/-- No competing data-plan transition is available for an admitted written call. -/
theorem written_call_not_data (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (arguments : List Atom)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : callable registry head = true) :
    ¬ Transition registry (atExpression base bindings (.expression (.symbol head :: arguments)))
      { base with control := .arguments bindings .data (.symbol head :: arguments) [] 0 } := by
  intro wrong
  have computed := transition_step wrong
  rw [written_call_step registry base bindings head arguments ordinary recognized] at computed
  have controls := congrArg (fun result => result.map Configuration.control) computed
  simp at controls

/-- Arbitrarily nested evaluating contexts reach the admitted function plan. -/
theorem current_written_call_in_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (head : String) (arguments : List Atom)
    (frames : List Frame) (ready : frames? bindings context = some frames)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : callable (codeRegistry registry base.privateCode) head = true) :
    Relation.ReflTransGen (Transition registry)
      (atExpression base bindings (plug context (.expression (.symbol head :: arguments))))
      { base with
        control := .arguments bindings (.function head) arguments [] 0
        frames := frames ++ base.frames } := by
  have reached := hole_step_reached registry context base bindings
    (.expression (.symbol head :: arguments)) frames ready
    { base with control := .arguments bindings (.function head) arguments [] 0, frames := [] }
    (.call_enter rfl ordinary recognized)
  simpa [appendFrames] using reached

theorem written_call_in_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (head : String) (arguments : List Atom)
    (frames : List Frame) (ready : frames? bindings context = some frames)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : callable registry head = true) :
    Relation.ReflTransGen (Transition registry)
      (atExpression base bindings (plug context (.expression (.symbol head :: arguments))))
      {base with
        control := .arguments bindings (.function head) arguments [] 0
        frames := frames ++ base.frames} :=
  current_written_call_in_context registry context base bindings head arguments frames ready ordinary
    (callable_with_privateCode registry base.privateCode head recognized)

/-- Unknown heads keep the source's data application rule, including its argument policy. -/
theorem unknown_head_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (head : String) (arguments : List Atom)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (unknown : callable (codeRegistry registry base.privateCode) head = false) :
    step registry (atExpression base bindings (.expression (.symbol head :: arguments))) =
      some { base with control := .arguments bindings .data (.symbol head :: arguments) [] 0 } := by
  exact transition_step (.data_enter rfl ordinary unknown)

/-- Quotation returns a value packet; it does not invoke the term being held. -/
theorem quote_is_value (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (term : Atom) :
    step registry (atExpression base bindings (.expression [.symbol "quote", term])) =
      some { base with control := .returned [⟨resolve bindings term, bindings⟩] } :=
  transition_step (.quote_enter rfl)

theorem held_variable_is_value (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (name : String) :
    step registry (atExpression base bindings (.var name)) =
      some { base with control := .returned [⟨resolve bindings (.var name), bindings⟩] } :=
  transition_step (.value_variable rfl)

namespace Controls

def emptyRegistry : SpaceSemantics.Program := { equations := [], declarations := [] }
def atom (name : String) : Atom := .symbol name
def call (name : String) (arguments : List Atom) : Atom := .expression (.symbol name :: arguments)
def var (name : String) : Atom := .var name

def bindingVisibleOutside : Atom :=
  call "let" [var "r", call "let" [var "x", atom "bound", atom "a"], var "x"]

def bindingErased : Atom := call "let" [var "r", atom "a", var "x"]

/-- A variable unused in the immediate body can still constrain the enclosing continuation. -/
theorem binding_unused_in_body_is_not_globally_unused :
    observed (run emptyRegistry 40 (start Effects.empty bindingVisibleOutside)) =
      .answers [atom "bound"] ∧
    observed (run emptyRegistry 40 (start Effects.empty bindingErased)) =
      .answers [var "x"] := by
  decide +kernel

def heldPrinting : Atom := call "quote" [call "println!" [atom "should-not-print"]]

theorem quotation_does_not_run_print :
    shown (run emptyRegistry 20 (start Effects.empty heldPrinting)) =
      .printed [] [call "println!" [atom "should-not-print"]] := by decide +kernel

theorem unquoted_print_is_an_effect :
    shown (run emptyRegistry 20 (start Effects.empty (call "println!" [atom "should-not-print"]))) =
      .printed [atom "should-not-print"] [Effects.boolean true] := by decide +kernel

def malformedCase : Atom := call "case" [call "println!" [atom "unreached"], .expression [atom "bad-row"]]

theorem malformed_case_does_not_enter_its_hole :
    shown (run emptyRegistry 20 (start Effects.empty malformedCase)) =
      .fault (.invalidArguments "case") := by decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaActivation
