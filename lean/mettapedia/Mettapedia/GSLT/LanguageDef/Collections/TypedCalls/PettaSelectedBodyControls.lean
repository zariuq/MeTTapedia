import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyExecution
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldBodyControls

/-!
# Actual clause-frontier body-mode controls

These run fresh selected clauses, not a supplied formed result or a body
oracle. A foreign-arity Atom row must not suppress an effect; held syntax
must not execute it. The actual predicate delimiter and duplicate equation
occurrences survive the lowered entry. Native installation remains separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaHeldBodyControls (num text call effectBody emptyBody services)
open PettaSelectedBodyFrontier (frontier schedule)

def declaration (parameters : List Atom) (range : Atom) : Atom :=
  call ":" [.symbol "raw", call "->" (parameters ++ [range])]

def equation (body : Atom) : SpaceSemantics.Equation := ⟨"raw", [.var "x"], body⟩

def program (held duplicate foreign : Bool) (body : Atom) : SpaceSemantics.Program :=
  {equations := if duplicate then [equation body, equation body] else [equation body],
    declarations := [declaration [.symbol "Atom"] (.symbol (if held then "Atom" else "%Undefined%"))] ++
      if foreign then [declaration [] (.symbol "Atom")] else []}

def caller : DControl := ⟨[], [], .var "out", ∅, 7⟩
def frame (held : Bool) : CallFrame :=
  ⟨"raw", ⟨[.sym "Atom"], .sym (if held then "Atom" else "%Undefined%")⟩,
    [], [num 4], 1, [], [], .var "out", 0, .var "out", 1, .body⟩

def selected (held duplicate foreign : Bool) (body : Atom) : List (Nat × Control) :=
  frontier (program held duplicate foreign body) caller "raw" [num 4] (.var "out") []

def placedChoices (p : SpaceSemantics.Program) (held : Bool) (choices : List (Nat × Control)) : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded p, output := [text "before"]},
    [⟨choices.map (fun (occurrence, control) =>
      (predicateEntry 0 control, ⟨(), [frame held]⟩, [3, occurrence])), [], none⟩]⟩)

def initial (held duplicate foreign : Bool) (body : Atom) : State Unit :=
  placedChoices (program held duplicate foreign body) held (selected held duplicate foreign body)

def observe (p : SpaceSemantics.Program) (source : State Unit) : Option (List Atom × List Atom) :=
  match (PettaOccurrenceOverlay.machine services .eagerValue p).run 40 source with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem actual_selected_held_body_preserves_code_as_data :
    observe (program true false false effectBody) (initial true false false effectBody) =
      some ([effectBody], [text "before"]) := by cbv

theorem actual_selected_eager_body_performs_its_effect :
    observe (program false false false effectBody) (initial false false false effectBody) =
      some ([Effects.boolean true], [text "before", text "must-not-run"]) := by cbv

theorem a_foreign_nullary_Atom_cannot_suppress_the_unary_body_effect :
    observe (program false false true effectBody) (initial false false true effectBody) =
      some ([Effects.boolean true], [text "before", text "must-not-run"]) := by cbv

def headWideMutation : State Unit :=
  let p := program false false true effectBody
  let choices := (ClauseChoice.choices p caller "raw" [num 4] (.var "out") []).map fun (occurrence, next) =>
    (occurrence, schedule true next)
  placedChoices p false choices

theorem a_head_wide_mode_mutation_suppresses_a_real_source_effect :
    observe (program false false true effectBody) headWideMutation = some ([effectBody], [text "before"]) := by cbv

theorem held_empty_has_one_syntax_answer :
    observe (program true false false emptyBody) (initial true false false emptyBody) =
      some ([emptyBody], [text "before"]) := by cbv

theorem evaluated_empty_has_no_answer :
    observe (program false false false emptyBody) (initial false false false emptyBody) =
      some ([], [text "before"]) := by cbv

theorem duplicate_held_equations_keep_both_occurrences :
    (selected true true false effectBody).map Prod.fst = [0, 1] ∧
      observe (program true true false effectBody) (initial true true false effectBody) =
        some ([effectBody, effectBody], [text "before"]) := by cbv

theorem duplicate_eager_equations_keep_both_effects :
    observe (program false true false effectBody) (initial false true false effectBody) =
      some ([Effects.boolean true, Effects.boolean true],
        [text "before", text "must-not-run", text "must-not-run"]) := by cbv

def reachedCut : Option Nat :=
  match (PettaOccurrenceOverlay.machine services .eagerValue (program true false false effectBody)).run 3
      (initial true false false effectBody) with
  | (_, .exhausted final) => do
      let scope ← final.2.scopes.head?
      let work ← scope.frontier.head?
      if work.1.goals.isEmpty then some work.1.cutBoundary else none
  | _ => none

theorem the_real_predicate_delimiter_is_restored_before_guard_dispatch : reachedCut = some 7 := by cbv

def rejecting : SpaceSemantics.Program :=
  {program true false false effectBody with equations := [⟨"raw", [num 2], effectBody⟩]}

theorem holding_does_not_turn_a_failed_head_match_into_a_selected_body :
    frontier rejecting caller "raw" [num 4] (.var "out") [] = [] := by cbv

theorem another_arity_does_not_acquire_a_body_by_holding :
    frontier (program true false false effectBody) caller "raw" [] (.var "out") [] = [] := by cbv

theorem the_selected_frontier_has_its_independent_entry_derivation (occurrence : Nat) (next : Control)
    (member : (occurrence, next) ∈ selected true false false effectBody) :
    PettaSelectedBodyFrontier.Entry (program true false false effectBody) caller "raw" [num 4]
      (.var "out") [] occurrence next :=
  (PettaSelectedBodyFrontier.member_iff ..).mp member

def first : DControl := ((selected true false false effectBody)[0]'(by cbv)).2

def returned (bindings : Equations) : State Unit :=
  Bridges.ClosedOnceQueryFrame.placed (Allocator.empty 8 64)
    {state := Effects.loaded (program true false false effectBody), output := [text "before"]}
    (⟨[], [], none⟩ : Scope Unit) [] {first with bindings, goals := []}
    (⟨(), [frame true]⟩ : Context Unit) [3, 0] []

/-- The general execution theorem is applied to the actual selected record,
not merely to a hand-authored body-state fixture. -/
theorem the_source_selected_run_earns_a_consistent_return :
    ∃ bindings environment,
      refine first.bindings effectBody (frame true).callDestination = some bindings ∧
      resolve bindings = some environment ∧
      (PettaOccurrenceOverlay.machine services .eagerValue (program true false false effectBody)).run 3
        (initial true false false effectBody) = ([], .exhausted (returned bindings)) := by
  have pairEq : ((selected true false false effectBody)[0]'(by cbv)) = (0, first) := by cbv
  have selectedMember : (0, first) ∈ selected true false false effectBody := by
    rw [← pairEq]
    exact List.getElem_mem _
  have held : SelectedBodyPolicy.descriptorHolding .complete 1
      ((PettaSelectedBodyDeclarations.family (program true false false effectBody) "raw").map
        CallGuardOptimization.compile) = true := by cbv
  obtain ⟨chosen, row, named, arity, outcome⟩ := PettaSelectedBodyExecution.selected_held_outcome
    services .eagerValue (program true false false effectBody) (Allocator.empty 8 64)
    {state := Effects.loaded (program true false false effectBody), output := [text "before"]}
    (⟨[], [], none⟩ : Scope Unit) [] caller first (⟨(), [frame true]⟩ : Context Unit) [3, 0] []
    (frame true) [] "raw" [num 4] 0 0 selectedMember held rfl rfl rfl rfl
  have same : chosen = equation effectBody := by simpa only [program, Bool.false_eq_true, ↓reduceIte,
    List.getElem?_cons_zero, Option.some.injEq] using row.symm
  subst chosen
  dsimp only at outcome
  have bodyEq : ClauseChoice.freshBody caller 0 (equation effectBody) = effectBody := by
    simp [ClauseChoice.freshBody, equation, effectBody, call, text,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  rw [bodyEq] at outcome
  have accepted : (refine first.bindings effectBody (frame true).callDestination).isSome = true := by cbv
  cases result : refine first.bindings effectBody (frame true).callDestination with
  | none => rw [result] at accepted; cases accepted
  | some bindings =>
    rw [result] at outcome
    obtain ⟨environment, resolved, run, guarded⟩ := outcome
    refine ⟨bindings, environment, rfl, resolved, ?_⟩
    have initialEq : Bridges.ClosedOnceQueryFrame.placed (Allocator.empty 8 64)
        {state := Effects.loaded (program true false false effectBody), output := [text "before"]}
        (⟨[], [], none⟩ : Scope Unit) [] (predicateEntry 0 first)
        (⟨(), [frame true]⟩ : Context Unit) [3, 0] [] = initial true false false effectBody := by cbv
    simpa only [initialEq, returned] using run

def older : Work Unit :=
  (⟨[], [.evaluate (.symbol "older") (.var "outside")], .var "outside", ∅, 0⟩, ⟨(), []⟩, [9])

def refusal : State Unit :=
  let p := program true false false effectBody
  let pinned := {caller with bindings := [(.var "out", .symbol "pinned")]}
  let choices := frontier p pinned "raw" [num 4] (.var "out") []
  let work : List (Work Unit) := choices.map fun (occurrence, next) =>
    (predicateEntry 0 next, ⟨(), [frame true]⟩, [3, occurrence])
  (Allocator.empty 8 64, ⟨{state := Effects.loaded p, output := [text "before"]},
    [⟨work ++ [older], [], none⟩]⟩)

theorem a_refused_selected_return_preserves_the_older_alternative :
    observe (program true false false effectBody) refusal = some ([.symbol "older"], [text "before"]) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyControls
