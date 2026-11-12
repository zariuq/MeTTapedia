import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRun
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataControls

/-!
# Actual-source controls for effectful compound returns

The checked formal is a constructor pattern, not a replacement variable.
The body can print, select a branch, select duplicate query occurrences,
or fail before the constructor is returned. These bounded controls execute
the maintained owned source machine. The all-budget and retained-state
controls instantiate its general source theorem, not a native C plan codec.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open DestinationDataRecipe
open DestinationDataReturnState
open DestinationDataControls (num text call held recipe expected)

def effectBody : Atom := call "let" [.var "ignored", call "println!" [text "prefix"],
  call "if" [Effects.boolean true, recipe, call "empty" []]]

def queryBody : Atom := call "match" [.symbol "&self", call "row" [num 9], effectBody]

def failedBody : Atom := call "let" [.var "ignored", call "empty" [], recipe]

def program (body : Atom) : SpaceSemantics.Program :=
  {equations := [⟨"keep", [recipe], body⟩], declarations := [],
    facts := [call "row" [num 9], call "row" [num 9]], layout := [.equation, .fact, .fact]}

def caller : Control := {bindings := [], goals := [], destination := .var "result"}

def choices (body : Atom) : List (Nat × Control) :=
  ClauseChoice.choices (program body) caller "keep" [expected] caller.destination []

def initial (body : Atom) : ScopedCursor Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.loaded (program body), [], []⟩,
    [⟨(choices body).map (fun choice => (predicateEntry 0 choice.2, (), [choice.1])), [], none⟩]⟩)

def observe (body : Atom) (fuel : Nat) : Option (List Atom × List Atom) :=
  match (ScopedQuerySource.ownedMachine .eagerValue (program body)).run fuel (initial body) with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem recipe_is_data (body : Atom) : Recipe (program body) recipe := by
  apply Recipe.named "Cell" [.var "input", .symbol "Nil"] rfl rfl (by cbv) (by decide)
  intro child member
  rcases List.mem_cons.mp member with rfl | later
  · exact .variableValue _
  · cases List.mem_singleton.mp later
    exact .symbol _

theorem effect_body_checked : ScopedReturnSyntax.checksSurfaceReturn recipe 4 effectBody = true := by cbv

theorem query_body_checked : ScopedReturnSyntax.checksSurfaceReturn recipe 5 queryBody = true := by cbv

theorem failed_body_checked : ScopedReturnSyntax.checksSurfaceReturn recipe 2 failedBody = true := by cbv

theorem a_fresh_compound_body_earns_the_entry_contract (next : Control)
    (selected : ClauseChoice.attempt caller "keep" [expected] caller.destination [] 0
      ⟨"keep", [recipe], queryBody⟩ = some next) :
    AliasHolds (program queryBody) expected (predicateEntry 0 next) := by
  exact DestinationDataReturnEntry.selected_predicate_entry (program queryBody) caller "keep" [expected]
    caller.destination [] 0 0 ⟨"keep", [recipe], queryBody⟩ next 0 expected recipe 5 selected rfl rfl
    (recipe_is_data queryBody) query_body_checked rfl

theorem the_prefix_runs_before_the_compound_return :
    observe effectBody 40 = some ([expected], [text "prefix"]) := by cbv

theorem captured_executable_data_stays_held :
    observe effectBody 40 ≠ some ([call "Cell" [num 3, .symbol "Nil"]], [text "prefix"]) := by
  rw [the_prefix_runs_before_the_compound_return]
  decide +kernel

theorem finite_exhaustion_is_not_success : observe effectBody 2 = none := by cbv

theorem checked_return_syntax_does_not_assume_a_successful_body :
    observe failedBody 20 = some ([], []) := by cbv

theorem duplicate_queries_keep_both_returns_and_both_effects :
    observe queryBody 80 = some ([expected, expected], [text "prefix", text "prefix"]) := by cbv

def immediateReturn : Atom := recipe

theorem deleting_the_effect_prefix_is_not_an_equivalent_lowering :
    observe immediateReturn 20 = some ([expected], []) ∧
      observe immediateReturn 20 ≠ observe effectBody 40 := by
  have direct : observe immediateReturn 20 = some ([expected], []) := by cbv
  exact ⟨direct, by rw [direct, the_prefix_runs_before_the_compound_return]; decide +kernel⟩

theorem a_calling_child_is_not_constructor_evidence : ¬ Recipe (program effectBody) held := by
  intro data
  cases data with
  | named head arguments ordinary localForm inert surface children =>
      have active : callable (program effectBody) "+" = true := by decide
      rw [active] at inert
      cases inert
  | tuple children noHead parts => exact (noHead "+" [num 1, num 2] rfl).elim

theorem initial_obligation (body : Atom) (inspectionFuel : Nat)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel body = true) :
    DestinationDataReturnRun.CursorGood (program body) (fun _ : Unit => expected) (initial body) := by
  refine ⟨.root _ _, .root _ ?_⟩
  intro work member
  obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨equation, row, chosen⟩ :=
    (ClauseChoice.mem_choices_iff (program body) caller "keep" [expected] caller.destination [] choice.1 choice.2).mp selected
  have same : equation = ⟨"keep", [recipe], body⟩ := by
    simpa only [program, List.mem_singleton] using List.mem_of_getElem? row
  subst equation
  exact DestinationDataReturnEntry.selected_predicate_entry (program body) caller "keep" [expected]
    caller.destination [] choice.1 0 ⟨"keep", [recipe], body⟩ choice.2 0 expected recipe inspectionFuel chosen
    rfl rfl (recipe_is_data body) checked rfl

theorem every_finite_query_budget_reads_the_matched_compound_input (fuel : Nat) :
    let packets := ((ScopedQuerySource.ownedMachine .eagerValue (program queryBody)).run fuel (initial queryBody)).1
    packets.map CollectedAnswer.value = List.replicate packets.length expected := by
  dsimp only
  have valid := initial_obligation queryBody 5 query_body_checked
  have emitted := DestinationDataReturnRun.run_packets_read_input (fun _ : Unit => expected)
    (program queryBody) fuel (initial queryBody) valid.1 valid.2
  apply List.map_eq_replicate_iff.mpr
  intro packet present
  obtain ⟨context, environment, resolved, observed⟩ := emitted packet present
  exact observed.trans (ProtectedSlots.read_ground environment expected
    (by simp [expected, held, call, num, encode, Mettapedia.Logic.LP.Term.isGround, Fin.forall_fin_succ]))

theorem every_query_pause_retains_the_obligation (fuel : Nat) :
    match ((ScopedQuerySource.ownedMachine .eagerValue (program queryBody)).run fuel (initial queryBody)).2 with
    | .finished final | .exhausted final | .suspended _ final | .stuck final =>
        DestinationDataReturnRun.CursorGood (program queryBody) (fun _ : Unit => expected) final
    | .faulted => False := by
  have retained := DestinationDataReturnRun.run_retains_obligation (fun _ : Unit => expected) (program queryBody) fuel
    (initial queryBody) (initial_obligation queryBody 5 query_body_checked)
  cases outcome : ((ScopedQuerySource.ownedMachine .eagerValue (program queryBody)).run fuel (initial queryBody)).2 <;>
    (simp only [outcome] at retained <;> exact retained)

def scalarProgram : SpaceSemantics.Program :=
  {equations := [⟨"keepScalar", [.symbol "Nil"],
      call "match" [.symbol "&self", call "row" [num 9], .symbol "Nil"]⟩],
    declarations := [], facts := [call "row" [num 9], call "row" [num 9]], layout := [.equation, .fact, .fact]}

def scalarInitial : ScopedCursor Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.loaded scalarProgram, [], []⟩,
    [⟨(ClauseChoice.choices scalarProgram caller "keepScalar" [.symbol "Nil"] caller.destination []).map
      (fun choice => (predicateEntry 0 choice.2, (), [choice.1])), [], none⟩]⟩)

theorem scalar_query_fusion_keeps_both_occurrences :
    (((ScopedQuerySource.ownedMachine .eagerValue scalarProgram).run 30 scalarInitial).1).map CollectedAnswer.value =
      [.symbol "Nil", .symbol "Nil"] := by cbv

theorem scalar_fusion_is_not_used_for_a_constructor_template :
    ConstantQuerySource.isScalar recipe = false := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnControls
