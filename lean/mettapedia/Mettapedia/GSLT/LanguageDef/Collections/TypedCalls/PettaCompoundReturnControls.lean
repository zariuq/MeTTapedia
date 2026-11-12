import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundProducedEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices
import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler

/-!
# Compound returns with live source guards and typed prefix calls

The named-call controls start without preinstalled frames. Declarations,
type derivations and result stores come from the loaded source world. The
executing helper has an Undefined result; a literal Atom result holds an
ordinary RHS in production PeTTa. The eager-overlay counterexample below
keeps that unproved body-policy correspondence visible.
The local frame countermodel separately shows why a non-callable constructor
cannot be captured as a typed prefix call. It is not a source-reachability
claim for an invented call row.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def num (value : Int) : Atom := .grounded (.int value)
def text (value : String) : Atom := .grounded (.string value)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def recipe : Atom := call "Cell" [.var "number", .symbol "Nil"]
def argument : Atom := call "Cell" [num 4, .symbol "Nil"]
def body : Atom := call "let" [.var "printed", call "ping" [], recipe]
def keepEquation : SpaceSemantics.Equation := ⟨"keepCell", [recipe], body⟩
def pingEquation : SpaceSemantics.Equation := ⟨"ping", [], call "println!" [text "body"]⟩

def program (many bad : Bool) : SpaceSemantics.Program :=
  let declarations :=
    [PettaSourceTypeRows.declaration "keepCell" (arrow [.sym "Atom"] (.sym (if bad then "Other" else "Box"))),
     PettaSourceTypeRows.declaration "ping" (arrow [] (.sym "%Undefined%")),
     PettaSourceTypeRows.declaration "Nil" (.sym "Tail"),
     PettaSourceTypeRows.declaration "Cell" (arrow [.sym "Number", .sym "Tail"] (.sym "Box"))] ++
    if many then [PettaSourceTypeRows.declaration "Cell" (arrow [.sym "_", .sym "Tail"] (.sym "Box"))] else []
  {equations := [keepEquation, pingEquation], declarations,
    layout := [.equation, .equation] ++ List.replicate declarations.length .declaration}

def services : Services Unit := PettaSourceTypeServices.services []

def initial (many bad older : Bool) : State Unit :=
  let control : DControl := ⟨[], [.evaluate (call "keepCell" [argument]) (.var "result")], .var "result", ∅, 9⟩
  let other : Work Unit :=
    (⟨[], [.evaluate (.symbol "older") (.var "outside")], .var "outside", ∅, 0⟩, ⟨(), []⟩, [99])
  (Allocator.empty 8 64, ⟨{state := Effects.loaded (program many bad), output := [text "before"]},
    [⟨(control, ⟨(), []⟩, []) :: (if older then [other] else []), [], none⟩]⟩)

def observe (operations : Services Unit) (many bad : Bool) (source : State Unit) : Option (List Atom × List Atom) :=
  match (PettaOccurrenceOverlay.machine operations .eagerValue (program many bad)).run 120 source with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem compound_head_is_checked :
    Bridges.DestinationDataReturnFunction.checksHead (program false false) "keepCell" 0 4 = true := by cbv

theorem variable_only_check_does_not_silently_accept_the_compound_formal :
    Bridges.ScopedReturnFunction.checksHead (program false false) "keepCell" 0 4 = false := by cbv

theorem executing_helper_has_no_raw_body_declaration :
    OutputPlan.rawOutput (program false false) "ping" 0 = false := by cbv

theorem the_data_checker_rejects_executable_children :
    Bridges.DestinationDataReturnFunction.checksData (program false false) (call "Cell" [call "ping" [], .symbol "Nil"]) = false := by cbv

theorem duplicate_equations_remain_checked_occurrences :
    Bridges.DestinationDataReturnFunction.checksHead
      {program false false with equations := [keepEquation, keepEquation, pingEquation]} "keepCell" 0 4 = true := by cbv

theorem an_absent_head_has_no_vacuous_certificate :
    Bridges.DestinationDataReturnFunction.checksHead (program false false) "missing" 0 4 = false := by cbv

theorem one_wrong_return_body_rejects_the_head :
    Bridges.DestinationDataReturnFunction.checksHead
      {program false false with equations := [keepEquation, ⟨"keepCell", [recipe], .symbol "wrong"⟩]}
      "keepCell" 0 4 = false := by cbv

theorem named_call_with_a_typed_prefix_returns_the_compound_value :
    observe services false false (initial false false false) = some ([argument], [text "before", text "body"]) := by cbv

theorem independent_constructor_typings_keep_result_multiplicity :
    observe services true false (initial true false false) = some ([argument, argument], [text "before", text "body"]) := by cbv

theorem result_refusal_keeps_the_older_host_alternative :
    observe services false true (initial false true true) = some ([.symbol "older"], [text "before", text "body"]) := by cbv

def erasedRange : Services Unit := {services with
  rows := fun world _ head arguments =>
    match PettaSourceTypeRows.lookup [] world head arguments with
    | .typed rows => .typed (rows.map fun row => {row with range := .sym "%Undefined%"})
    | other => other}

theorem dropping_the_result_guard_invents_a_result :
    observe erasedRange false true (initial false true true) = some ([argument, .symbol "older"], [text "before", text "body"]) := by cbv

def missingResult : Services Unit := {services with
  orderedGuard := fun world index store expected value =>
    if index = 1 then none else PettaSourceTypeServices.orderedGuard [] world index store expected value
  guard_exact := by
    intro world index store expected value answers served
    by_cases missing : index = 1
    · simp [missing] at served
    · exact PettaSourceTypeServices.orderedGuard_exact [] world index store expected value answers
        (by simpa only [missing, if_false] using served)}

def suspended : Option (State Unit) :=
  match ((PettaOccurrenceOverlay.machine missingResult .eagerValue (program false false)).run 120 (initial false false false)).2 with
  | .suspended (.guard "keepCell" 1 _ _) saved => some saved
  | _ => none

theorem missing_result_service_retains_the_compound_call : suspended.isSome = true := by cbv

def resumed : Option (List Atom × List Atom) := suspended.bind (observe services false false)
def replayed : Option (List Atom × List Atom) := do
  let saved ← suspended
  let fresh := initial false false false
  observe services false false (fresh.1, {fresh.2 with world := saved.2.world})

theorem resumed_result_service_does_not_repeat_the_prefix :
    resumed = some ([argument], [text "before", text "body"]) := by cbv

theorem restarting_the_named_call_repeats_the_completed_effect :
    replayed = some ([argument], [text "before", text "body", text "body"]) := by cbv

def debtControl : DControl := ⟨[], [.evaluate recipe (.var "out")], .var "out", ∅, 0⟩
def prefixControl : DControl :=
  {debtControl with goals := .evaluate (call "ping" []) (.var "temporary") :: debtControl.goals}

private theorem recipe_is_data : Bridges.DestinationDataRecipe.Recipe (program false false) recipe :=
  Bridges.DestinationDataReturnFunction.checksData_sound _ _ (by cbv)

private theorem prefix_alias : Bridges.DestinationDataReturnState.AliasHolds (program false false) recipe prefixControl := by
  refine ⟨recipe, recipe_is_data, fun _ _ => rfl, .inr (.inl ?_)⟩
  exact (Bridges.ScopedReturnObligation.Pending.evaluation recipe [] .leaf).prepend_evaluation (call "ping" []) (.var "temporary")

theorem a_real_callable_prefix_captures_the_pending_compound_return :
    let work := rowWork prefixControl (⟨(), []⟩ : Context Unit) [] 1 "ping" [] (.var "temporary") debtControl.goals ⟨[], .sym "Atom"⟩ 0
    PettaCompoundReturnFrames.Frames (program false false) recipe work.1 work.2.1.calls := by
  exact PettaCompoundReturnFrames.row_work_captures_return recipe prefixControl (⟨(), []⟩ : Context Unit) [] 1
    "ping" [] (.var "temporary") debtControl.goals ⟨[], .sym "Atom"⟩ 0 prefix_alias rfl (by decide) (by decide)

theorem a_constructor_cannot_be_captured_as_a_prefix_call :
    let work := rowWork debtControl (⟨(), []⟩ : Context Unit) [] 1 "Cell" [.var "number", .symbol "Nil"]
      (.var "out") [] ⟨[.sym "Atom", .sym "Atom"], .sym "Atom"⟩ 0
    ¬ PettaCompoundReturnFrames.Frames (program false false) recipe work.1 work.2.1.calls := by
  dsimp only
  intro held
  change Bridges.DestinationDataReturnState.AliasHolds (program false false) recipe {debtControl with goals := []} at held
  obtain ⟨pattern, data, returning⟩ := held
  have readout := Bridges.DestinationDataReturnState.terminal_reads returning rfl
    (Mettapedia.Logic.LP.Subst.id signature) (by intro pair member; cases member)
  unfold EagerDFS.Destination.read at readout
  simp only [Mettapedia.Logic.LP.Subst.applyTerm_id, decode_encode] at readout
  cases readout

theorem unpaid_constructor_work_is_not_an_old_alias_certificate :
    ¬ Bridges.ScopedReturnLocal.AliasHolds recipe debtControl := by
  rintro ⟨name, protectedRead, returning⟩
  have readout := protectedRead (Mettapedia.Logic.LP.Subst.id signature) (by intro pair member; cases member)
  unfold EagerDFS.Destination.read at readout
  simp only [Mettapedia.Logic.LP.Subst.applyTerm_id, decode_encode] at readout
  cases readout

def readyBody (source : State Unit) : Bool :=
  match source.2.scopes with
  | [current] =>
      match current.frontier with
      | [(control, context, _)] =>
          match context.calls with
          | [frame] =>
              frame.head == "keepCell" && frame.phase == .body && frame.index == 1 && frame.ready == [argument] &&
                control.goals == [.invoke frame.head frame.ready frame.callDestination] &&
                control.destination == frame.callDestination && frame.scopeDepth == 1 &&
                ((resolve control.bindings).map (fun environment => read environment frame.callDestination)) == some (.var "result")
          | _ => false
      | _ => false
  | _ => false

theorem the_actual_producer_reaches_the_certified_entry_phase :
    (PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine services .eagerValue (program false false)).run 3 (initial false false false)).2).map readyBody =
      some true := by cbv

def atomHelperProgram : SpaceSemantics.Program :=
  {program false false with declarations := (program false false).declarations.map fun declaration =>
    if declaration == PettaSourceTypeRows.declaration "ping" (arrow [] (.sym "%Undefined%")) then
      PettaSourceTypeRows.declaration "ping" (arrow [] (.sym "Atom")) else declaration}

def atomHelperInitial : State Unit :=
  let source := initial false false false
  (source.1, {source.2 with world := {source.2.world with state := Effects.loaded atomHelperProgram}})

/-- The compiler's raw-body policy and this overlay's eager-body policy are
not the same instance. Guard correctness alone does not identify them. -/
theorem raw_body_policy_is_not_supplied_by_the_eager_overlay :
    OutputPlan.rawOutput atomHelperProgram "ping" 0 = true ∧
      observe services false false atomHelperInitial = some ([argument], [text "before", text "body"]) := by
  constructor <;> cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnControls
