import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnSyntax

/-!
# Held-body execution and policy-separation controls

These controls execute a compiler-formed body region in its retained typed
frame. They do not claim a complete named native call: selection of this
body mode and native execution escapes still require their own bridge.
The RHS contains an actual effect or failure expression, so replacing
quotation by eager execution is observably wrong.
-/

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def text (value : String) : Atom := .grounded (.string value)
def num (value : Int) : Atom := .grounded (.int value)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def effectBody : Atom := call "println!" [text "must-not-run"]
def emptyBody : Atom := call "empty" []

def equation (body : Atom) : SpaceSemantics.Equation := ⟨"raw", [.var "x"], body⟩
def program (body : Atom) : SpaceSemantics.Program :=
  {equations := [equation body],
    declarations := [PettaSourceTypeRows.declaration "raw" (arrow [.sym "Atom"] (.sym "Atom"))],
    layout := [.equation, .declaration]}
def compiler (body : Atom) : OutputPlan.Context := OutputPlan.Context.ofProgram (program body)
def result (body : Atom) : OutputPlan.Result :=
  ⟨OutputPlan.Supply.start (body :: [.var "x"]), OutputPlan.Plan.value body⟩

theorem effect_body_has_actual_held_formation :
    OutputPlan.EquationBodyRel (compiler effectBody) (equation effectBody) (result effectBody) := by
  apply OutputPlan.EquationBodyRel.held
  cbv

theorem empty_body_has_actual_held_formation :
    OutputPlan.EquationBodyRel (compiler emptyBody) (equation emptyBody) (result emptyBody) := by
  apply OutputPlan.EquationBodyRel.held
  cbv

theorem formed_body_exposes_quotation_not_execution :
    (OutputPlan.normalized (result effectBody)).execute = OutputPlan.hold effectBody :=
  PettaHeldBodyReturn.held_formation_executes_quote effect_body_has_actual_held_formation (by cbv)

def frame : CallFrame :=
  ⟨"raw", ⟨[.sym "Atom"], .sym "Atom"⟩, [], [num 4], 1, [], [], .var "out", 0, .var "out", 1, .body⟩
def services : Services Unit := PettaSourceTypeServices.services []
def bodyControl (body : Atom) : DControl :=
  ⟨[], [.evaluate (OutputPlan.normalized (result body)).execute (.var "out")], .var "out", ∅, 0⟩
def initial (body : Atom) : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded (program body), output := [text "before"]},
    [⟨[(bodyControl body, ⟨(), [frame]⟩, [3])], [], none⟩]⟩)

def observe (body : Atom) (source : State Unit) : Option (List Atom × List Atom) :=
  match (PettaOccurrenceOverlay.machine services .eagerValue (program body)).run 12 source with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem a_held_effect_body_is_returned_without_its_effect :
    observe effectBody (initial effectBody) = some ([effectBody], [text "before"]) := by cbv

theorem held_empty_is_data_not_absence :
    observe emptyBody (initial emptyBody) = some ([emptyBody], [text "before"]) := by cbv

def eagerMutation (body : Atom) : State Unit :=
  let source := initial body
  (source.1, {source.2 with scopes :=
    [⟨[({bodyControl body with goals := [.evaluate body (.var "out")]}, ⟨(), [frame]⟩, [3])], [], none⟩]})

theorem eager_mutation_runs_the_forbidden_body_effect :
    observe effectBody (eagerMutation effectBody) = some ([Effects.boolean true], [text "before", text "must-not-run"]) := by cbv

theorem eager_mutation_confuses_held_empty_with_failure :
    observe emptyBody (eagerMutation emptyBody) = some ([], [text "before"]) := by cbv

theorem eager_return_syntax_does_not_certify_the_raw_mode :
    Bridges.ScopedReturnSyntax.checksSurfaceReturn (.var "x") 2 emptyBody = true ∧
      observe emptyBody (initial emptyBody) = some ([emptyBody], [text "before"]) := by cbv

def older : Work Unit :=
  (⟨[], [.evaluate (.symbol "older") (.var "outside")], .var "outside", ∅, 0⟩, ⟨(), []⟩, [9])
def clashingControl : DControl :=
  {bodyControl effectBody with bindings := [(.var "out", .symbol "pinned")]}
def clashing : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded (program effectBody), output := [text "before"]},
    [⟨[(clashingControl, ⟨(), [frame]⟩, [3]), older], [], none⟩]⟩)

theorem a_refused_return_equation_preserves_the_older_alternative :
    observe effectBody clashing = some ([.symbol "older"], [text "before"]) := by cbv

theorem compiled_body_reaches_the_existing_guard (bindings : Equations) (environment : Environment)
    (accepted : refine [] effectBody frame.callDestination = some bindings)
    (resolved : resolve bindings = some environment) :
    let scope : Scope Unit := ⟨[], [], none⟩
    let world : EagerDFS.World := {state := Effects.loaded (program effectBody), output := [text "before"]}
    let reachedControl := {bodyControl effectBody with bindings, goals := [], destination := frame.callDestination}
    let reached := Bridges.ClosedOnceQueryFrame.placed (Allocator.empty 8 64) world scope [] reachedControl
      (⟨(), [frame]⟩ : Context Unit) [3] []
    PettaOccurrenceOverlay.step services .eagerValue (program effectBody) reached =
      consumeBody services reached {scope with frontier := [(reachedControl, ⟨(), [frame]⟩, [3])]}
        [] reachedControl (⟨(), [frame]⟩ : Context Unit) [3] [] frame [] (read environment effectBody) := by
  exact (PettaHeldBodyReturn.formed_held_body_then_guard services .eagerValue (program effectBody) (Allocator.empty 8 64)
    {state := Effects.loaded (program effectBody), output := [text "before"]} ⟨[], [], none⟩ []
    (bodyControl effectBody) (⟨(), [frame]⟩ : Context Unit) [3] [] frame [] bindings environment
    (compiler effectBody) (equation effectBody) (result effectBody) effect_body_has_actual_held_formation (by cbv)
    rfl rfl rfl accepted resolved).2

def compoundRecipe : Atom := call "Raw" [.var "n"]
def compoundArgument : Atom := call "Raw" [call "println!" [text "captured-code"]]
def compoundEquation : SpaceSemantics.Equation := ⟨"raw", [compoundRecipe], compoundRecipe⟩
def compoundProgram : SpaceSemantics.Program :=
  {equations := [compoundEquation],
    declarations := [PettaSourceTypeRows.declaration "raw" (arrow [.sym "Atom"] (.sym "Atom"))],
    layout := [.equation, .declaration]}
def compoundCompiler : OutputPlan.Context := OutputPlan.Context.ofProgram compoundProgram
def compoundResult : OutputPlan.Result :=
  ⟨OutputPlan.Supply.start (compoundRecipe :: [compoundRecipe]), OutputPlan.Plan.value compoundRecipe⟩
def compoundCaller : DControl := ⟨[], [], .var "out", ∅, 0⟩
def compoundSelected : Option Control :=
  ClauseChoice.attempt compoundCaller "raw" [compoundArgument] (.var "out") [] 0 compoundEquation
def compoundFrame : CallFrame := {frame with ready := [compoundArgument]}

theorem the_actual_compound_head_matches : compoundSelected.isSome = true := by cbv

theorem the_complete_held_equation_compiles :
    (OutputPlan.compileEquation compoundCompiler compoundEquation).isSome = true := by cbv

theorem the_compound_body_has_held_formation :
    OutputPlan.EquationBodyRel compoundCompiler compoundEquation compoundResult := by
  apply OutputPlan.EquationBodyRel.held
  cbv

theorem the_actual_compound_body_passes_mode_aware_admission :
    Bridges.FormedBodyReturnAdmission.checksHead compoundProgram "raw" 0 3 = true := by cbv

def compoundObservation : Option (List Atom × List Atom) := do
  let next ← compoundSelected
  let held := Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
    (ClauseChoice.rename compoundCaller 0 (ClauseChoice.clauseAtoms compoundEquation))
    (OutputPlan.normalized compoundResult).execute
  let source : State Unit := (Allocator.empty 8 64,
    ⟨{state := Effects.loaded compoundProgram, output := [text "before"]},
      [⟨[({next with goals := [.evaluate held (.var "out")]}, ⟨(), [compoundFrame]⟩, [3])], [], none⟩]⟩)
  match (PettaOccurrenceOverlay.machine services .eagerValue compoundProgram).run 12 source with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem fresh_compound_matching_returns_captured_code_as_data :
    compoundObservation = some ([compoundArgument], [text "before"]) := by cbv

def openArgument : Atom := call "Raw" [.var "later"]
def pinnedCaller : DControl := {compoundCaller with bindings := [(.var "out", compoundArgument)]}

def openObservation : Option (List Atom × List Atom) := do
  let next ← ClauseChoice.attempt pinnedCaller "raw" [openArgument] (.var "out") [] 0 compoundEquation
  let held := Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
    (ClauseChoice.rename pinnedCaller 0 (ClauseChoice.clauseAtoms compoundEquation))
    (OutputPlan.normalized compoundResult).execute
  let source : State Unit := (Allocator.empty 8 64,
    ⟨{state := Effects.loaded compoundProgram, output := [text "before"]},
      [⟨[({next with goals := [.evaluate held (.var "out")]},
        ⟨(), [{compoundFrame with ready := [openArgument]}]⟩, [3])], [], none⟩]⟩)
  match (PettaOccurrenceOverlay.machine services .eagerValue compoundProgram).run 12 source with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem an_open_input_is_read_after_the_actual_return_refinement :
    openObservation = some ([compoundArgument], [text "before"]) := by cbv

theorem freezing_the_open_input_before_return_would_be_wrong :
    openObservation ≠ some ([openArgument], [text "before"]) := by
  rw [an_open_input_is_read_after_the_actual_return_refinement]
  decide +kernel

theorem selected_compound_body_earns_its_guard_value (next : Control)
    (selected : compoundSelected = some next) (bindings : Equations) (environment : Environment)
    (accepted : refine next.bindings (ClauseChoice.freshBody compoundCaller 0 compoundEquation)
      compoundFrame.callDestination = some bindings)
    (resolved : resolve bindings = some environment) :
    let scope : Scope Unit := ⟨[], [], none⟩
    let world : EagerDFS.World := {state := Effects.loaded compoundProgram, output := [text "before"]}
    let reachedControl := {next with bindings, goals := [], destination := compoundFrame.callDestination}
    let reached := Bridges.ClosedOnceQueryFrame.placed (Allocator.empty 8 64) world scope [] reachedControl
      (⟨(), [compoundFrame]⟩ : Context Unit) [3] []
    PettaOccurrenceOverlay.step services .eagerValue compoundProgram reached =
      consumeBody services reached {scope with frontier := [(reachedControl, ⟨(), [compoundFrame]⟩, [3])]}
        [] reachedControl (⟨(), [compoundFrame]⟩ : Context Unit) [3] [] compoundFrame [] (read environment compoundArgument) := by
  exact (PettaHeldBodyEntry.checked_selected_held_body_then_guard services .eagerValue compoundProgram (Allocator.empty 8 64)
    {state := Effects.loaded compoundProgram, output := [text "before"]} ⟨[], [], none⟩ [] compoundCaller next
    (⟨(), [compoundFrame]⟩ : Context Unit) [3] [] compoundFrame [] "raw" [compoundArgument] 0 compoundEquation 0
    3 compoundArgument compoundCompiler compoundResult the_compound_body_has_held_formation
    the_actual_compound_body_passes_mode_aware_admission (by simp [compoundCompiler, OutputPlan.Context.ofProgram,
      compoundProgram]) rfl (by cbv) selected rfl bindings environment rfl rfl rfl accepted resolved).2

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyControls
