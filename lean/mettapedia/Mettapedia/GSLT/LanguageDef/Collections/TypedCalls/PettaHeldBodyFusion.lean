import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyExecution

/-!
# Ordinary held-body lowering fuses quotation into the actual return unifier

The native scheduling view selects a direct equate goal for an ordinary held
body. The source reaches that same goal after one administrative quotation
step. Their remaining runs are equal with this explicit one-step shift, in
the complete scoped typed machine and with arbitrary older work retained.

An explicit function wrapper is a separate native execution escape. The
classifier below exposes exactly where it differs from plain source holding;
the ordinary fusion refuses that case. It does not add the escape to PeTTa's
source language or establish native C storage and installation correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyFusion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination hiding Goal
open PettaOccurrenceOverlay
open Bridges.ClosedOnceQueryFrame (placed)
open SelectedBodyPolicy CallGuardOptimization

def explicitFunction : Atom → Bool
  | .expression [.symbol "function", _] => true
  | _ => false

inductive Route where
  | held
  | executed
  deriving DecidableEq

def sourceRoute (held : Bool) : Route := if held then .held else .executed

def nativeRoute (evaluateResult : Bool) (body : Atom) : Route :=
  if evaluateResult || explicitFunction body then .executed else .held

theorem routes_agree_iff (held : Bool) (body : Atom) :
    nativeRoute (!held) body = sourceRoute held ↔ held = false ∨ explicitFunction body = false := by
  cases held <;> cases detected : explicitFunction body <;> simp [nativeRoute, sourceRoute, detected]

def ordinaryGoal (supplied : Nat) (plans : List Plan) (body destination : Atom) : Option Goal :=
  if descriptorHolding .complete supplied plans && !explicitFunction body then some (.equate body destination) else none

theorem ordinary_goal_iff (program : SpaceSemantics.Program) (head : String) (supplied : Nat) (body destination : Atom) :
    ordinaryGoal supplied ((PettaSelectedBodyDeclarations.family program head).map compile) body destination = some (.equate body destination) ↔
      HoldsBody .complete supplied (PettaSelectedBodyDeclarations.family program head) ∧ explicitFunction body = false := by
  simp only [ordinaryGoal]
  by_cases held : descriptorHolding .complete supplied ((PettaSelectedBodyDeclarations.family program head).map compile) = true
  · rw [held]
    have literal := (descriptor_holding_has_the_source_judgment ..).mp held
    cases detected : explicitFunction body <;> simp [literal]
  · have notLiteral : ¬HoldsBody .complete supplied (PettaSelectedBodyDeclarations.family program head) := by
      intro literal
      exact held ((descriptor_holding_has_the_source_judgment ..).mpr literal)
    simp [held, notLiteral]

theorem quote_to_equate {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (older : List Goal)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    PettaOccurrenceOverlay.step services policy program
      (placed allocator world scope parents
        {caller with goals := .evaluate (OutputPlan.hold body) frame.callDestination :: older, destination := frame.callDestination} context origins pending) =
      .silent (placed allocator world scope parents
        {caller with goals := .equate body frame.callDestination :: older, destination := frame.callDestination} context origins pending) := by
  simp [PettaOccurrenceOverlay.step, delegate, sourceOwned, EagerDFS.eagerControlForm,
    calls, phase, depth, liftSource, Bridges.ScopedQuerySource.ownedStep,
    Bridges.ScopedQuerySource.ownershipStep, Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, OutputPlan.hold, OutputPlan.call]

theorem remaining_run_exact {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (older : List Goal)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) (budget : Nat) :
    (PettaOccurrenceOverlay.machine services policy program).run (budget + 1)
      (placed allocator world scope parents
        {caller with goals := .evaluate (OutputPlan.hold body) frame.callDestination :: older, destination := frame.callDestination} context origins pending) =
    (PettaOccurrenceOverlay.machine services policy program).run budget
      (placed allocator world scope parents
        {caller with goals := .equate body frame.callDestination :: older, destination := frame.callDestination} context origins pending) := by
  apply Machine.run_succ_silent
  exact congrArg some (quote_to_equate services policy program allocator world scope parents caller context origins pending
    frame outside body older calls phase depth)

theorem selected_native_goal_is_the_next_source_goal {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (older : List Goal)
    (head : String) (supplied : Nat) (goal : Goal)
    (selected : ordinaryGoal supplied ((PettaSelectedBodyDeclarations.family program head).map compile) body frame.callDestination = some goal)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    HoldsBody .complete supplied (PettaSelectedBodyDeclarations.family program head) ∧
      PettaOccurrenceOverlay.step services policy program
        (placed allocator world scope parents
          {caller with goals := .evaluate (OutputPlan.hold body) frame.callDestination :: older, destination := frame.callDestination} context origins pending) =
        .silent (placed allocator world scope parents
          {caller with goals := goal :: older, destination := frame.callDestination} context origins pending) := by
  have goalEq : goal = .equate body frame.callDestination := by
    unfold ordinaryGoal at selected
    split at selected
    · exact (Option.some.inj selected).symm
    · cases selected
  subst goal
  exact ⟨((ordinary_goal_iff ..).mp selected).1,
    quote_to_equate services policy program allocator world scope parents caller context origins pending frame outside body older calls phase depth⟩

def enqueue (supplied : Nat) (plans : List Plan) (selected : Control) : Option Control :=
  match selected.goals with
  | .evaluate body destination :: older =>
      (ordinaryGoal supplied plans body destination).map fun goal => {selected with goals := goal :: older}
  | _ => none

def frontier (program : SpaceSemantics.Program) (caller : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) : List (Nat × Control) :=
  (ClauseChoice.choices program caller head arguments destination older).filterMap fun (occurrence, selected) =>
    (enqueue arguments.length ((PettaSelectedBodyDeclarations.family program head).map compile) selected).map fun next => (occurrence, next)

inductive Entry (program : SpaceSemantics.Program) (caller : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) : Nat → Control → Prop where
  | held (occurrence : Nat) (equation : SpaceSemantics.Equation) (bindings : Equations)
      (row : program.equations[occurrence]? = some equation) (sameHead : equation.head = head)
      (matched : Refinement caller.bindings (.expression (.symbol head :: arguments))
        (ClauseChoice.freshPattern caller occurrence equation) (some bindings))
      (literal : HoldsBody .complete arguments.length (PettaSelectedBodyDeclarations.family program head))
      (ordinary : explicitFunction (ClauseChoice.freshBody caller occurrence equation) = false) :
      Entry program caller head arguments destination older occurrence
        {caller with bindings, goals := .equate (ClauseChoice.freshBody caller occurrence equation) destination :: older}

theorem frontier_member_iff (program : SpaceSemantics.Program) (caller : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (next : Control) :
    (occurrence, next) ∈ frontier program caller head arguments destination older ↔
      Entry program caller head arguments destination older occurrence next := by
  constructor
  · intro member
    obtain ⟨⟨index, selected⟩, present, emitted⟩ := List.mem_filterMap.mp member
    obtain ⟨equation, row, attempted⟩ := (ClauseChoice.mem_choices_iff ..).mp present
    by_cases named : equation.head = head
    · obtain ⟨bindings, matched, rfl⟩ := (ClauseChoice.attempt_iff caller head arguments destination older index equation named _).mp attempted
      simp only [enqueue, Option.map_map, Function.comp_def] at emitted
      obtain ⟨goal, chosen, pairEq⟩ := Option.map_eq_some_iff.mp emitted
      have indexEq : index = occurrence := congrArg Prod.fst pairEq
      subst index
      have goalEq : goal = .equate (ClauseChoice.freshBody caller occurrence equation) destination := by
        unfold ordinaryGoal at chosen
        split at chosen
        · exact (Option.some.inj chosen).symm
        · cases chosen
      subst goal
      have lowerEq : {caller with bindings, goals := .equate (ClauseChoice.freshBody caller occurrence equation) destination :: older} = next :=
        congrArg Prod.snd pairEq
      obtain ⟨literal, ordinary⟩ := (ordinary_goal_iff ..).mp chosen
      rw [← lowerEq]
      exact .held occurrence equation bindings row named matched literal ordinary
    · rw [ClauseChoice.wrong_head_not_selected _ _ _ _ _ _ _ named] at attempted
      cases attempted
  · intro entry
    cases entry with
    | held equation bindings row named matched literal ordinary =>
        have chosen := (ordinary_goal_iff program head arguments.length (ClauseChoice.freshBody caller occurrence equation) destination).mpr ⟨literal, ordinary⟩
        apply List.mem_filterMap.mpr
        refine ⟨(occurrence, {caller with bindings, goals := .evaluate (ClauseChoice.freshBody caller occurrence equation) destination :: older}), ?_, ?_⟩
        · exact (ClauseChoice.mem_choices_iff ..).mpr ⟨equation, row,
            (ClauseChoice.attempt_iff caller head arguments destination older occurrence equation named _).mpr ⟨bindings, matched, rfl⟩⟩
        · simp only [enqueue, chosen, Option.map_some]

theorem admitted_entry_has_the_actual_quoted_source {program : SpaceSemantics.Program} {caller : Control} {head : String}
    {arguments : List Atom} {destination : Atom} {older : List Goal} {occurrence : Nat} {next : Control}
    (entry : Entry program caller head arguments destination older occurrence next) :
    ∃ body bindings,
      PettaSelectedBodyFrontier.Entry program caller head arguments destination older occurrence
        {caller with bindings, goals := .evaluate (OutputPlan.hold body) destination :: older} ∧
      next = {caller with bindings, goals := .equate body destination :: older} := by
  cases entry with
  | held equation bindings row named matched literal ordinary =>
      exact ⟨ClauseChoice.freshBody caller occurrence equation, bindings,
        .held occurrence equation bindings row named matched literal, rfl⟩

theorem enqueue_keeps_the_reached_record (supplied : Nat) (plans : List Plan) (selected next : Control)
    (admitted : enqueue supplied plans selected = some next) :
    next.bindings = selected.bindings ∧ next.destination = selected.destination ∧
      next.reserved = selected.reserved ∧ next.cutBoundary = selected.cutBoundary := by
  unfold enqueue at admitted
  split at admitted
  · obtain ⟨goal, _, same⟩ := Option.map_eq_some_iff.mp admitted
    rw [← same]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases admitted

namespace Controls

def wrapper : Atom := .expression [.symbol "function", .expression [.symbol "return", .grounded (.int 3)]]

theorem the_explicit_escape_is_not_plain_holding :
    nativeRoute false wrapper = .executed ∧ sourceRoute true = .held ∧ nativeRoute false wrapper ≠ sourceRoute true := by decide

theorem a_quoted_wrapper_is_ordinary_data :
    explicitFunction (OutputPlan.hold wrapper) = false ∧ nativeRoute false (OutputPlan.hold wrapper) = .held := by decide

theorem a_bound_variable_is_not_an_authored_execution_marker :
    explicitFunction (.var "body") = false ∧ nativeRoute false (.var "body") = .held := by decide

theorem a_nonunary_function_spelling_is_not_the_escape :
    explicitFunction (.expression [.symbol "function", .symbol "a", .symbol "b"]) = false := by decide

theorem foreign_arity_Atom_rows_do_not_admit_a_held_return :
    ordinaryGoal 1 [compile ⟨[], .symbol "Atom"⟩, compile ⟨[.symbol "Number"], .symbol "Number"⟩]
      (.grounded (.int 3)) (.var "out") = none := by decide

theorem the_escape_is_not_misclassified_as_an_ordinary_fusion :
    ordinaryGoal 0 [compile ⟨[], .symbol "Atom"⟩] wrapper (.var "out") = none := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyFusion
