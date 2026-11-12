import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices

/-!
# Typed prefix calls, exact occurrences and retained guard boundaries

Declarations and ordered guards are read from the actual source world. The
body entry is earned by the source checker and clause selector. Counterexamples
distinguish return preservation from publication safety and correct resumption
from replay of an effectful body.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PettaOccurrenceOverlay

def num (n : Int) : Atom := .grounded (.int n)
def sym (name : String) : Atom := .symbol name
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def bind (name : String) (producer body : Atom) : Atom := call "let" [.var name, producer, body]

def body (tail : Atom) : Atom :=
  call "match" [sym "&self", call "row" [.var "r"],
    bind "ignored" (call "prefix" [.var "r"]) tail]

def prefixEquation (bad : Bool) : SpaceSemantics.Equation :=
  ⟨"prefix", [.var "value"], bind "printed" (call "println!" [.var "value"])
    (if bad then .grounded (.string "wrong") else .var "value")⟩

def program (bad polymorphic repeatedEquation : Bool) (rows : List Atom)
    (tail : Atom := .var "x") : SpaceSemantics.Program where
  equations := [⟨"keep", [.var "x"], body tail⟩, prefixEquation bad] ++ if repeatedEquation then [prefixEquation bad] else []
  declarations :=
    [PettaSourceTypeRows.declaration "prefix" (Row.asType
      (if polymorphic then ⟨[.var "a"], .var "a"⟩ else ⟨[.sym "Number"], .sym "Number"⟩))] ++
      if polymorphic then
        [PettaSourceTypeRows.declaration "dual" (.sym "Number"),
         PettaSourceTypeRows.declaration "dual" (.sym "Bool")] else []
  facts := rows.map fun value => call "row" [value]
  layout := List.replicate (2 + if repeatedEquation then 1 else 0) .equation ++
    List.replicate (1 + if polymorphic then 2 else 0) .declaration ++
    List.replicate rows.length .fact

def ordinary : SpaceSemantics.Program := program false false false [num 7, num 7, num 9]
def refused : SpaceSemantics.Program := program true false false [num 7, num 7, num 9]
def mixed : SpaceSemantics.Program := program false false false [num 7, .grounded (.string "bad"), num 9]
def multiple : SpaceSemantics.Program := program false true false [sym "dual", sym "dual"]
def repeated : SpaceSemantics.Program := program false true true [sym "dual", sym "dual"]

def services : Services Unit := PettaSourceTypeServices.services []
def control : DControl := ⟨[], [], .var "result", ∅, 0⟩

theorem program_balanced (bad polymorphic repeatedEquation : Bool) (rows : List Atom) (tail : Atom) :
    SpaceSemantics.Balanced (program bad polymorphic repeatedEquation rows tail) := by
  cases bad <;> cases polymorphic <;> cases repeatedEquation <;>
    simp [SpaceSemantics.Balanced, program, List.count_replicate]

def initial (operations : Services Unit) (source : SpaceSemantics.Program) : State Unit :=
  PettaCallerReturnEntry.enter operations source control "keep" [num 4] (.var "result") () []
    (Allocator.empty 8 64) ⟨Effects.loaded source, [], []⟩

def observe (operations : Services Unit) (source : SpaceSemantics.Program) (start : State Unit) :
    Option (List Atom × List Atom) :=
  let result := (machine operations .eagerValue source).run 1000 start
  match result.2 with
  | .finished final => some (result.1.map (·.value), final.2.world.output)
  | _ => none

def observed (operations : Services Unit) (source : SpaceSemantics.Program) : Option (List Atom × List Atom) :=
  observe operations source (initial operations source)

def missingResult : Services Unit := { services with
  orderedGuard := fun world index store expected value =>
    if index = 1 then none else PettaSourceTypeServices.orderedGuard [] world index store expected value
  guard_exact := by
    intro world index store expected value answers served
    by_cases missing : index = 1
    · simp [missing] at served
    · exact PettaSourceTypeServices.orderedGuard_exact [] world index store expected value answers
        (by simpa only [missing, if_false] using served) }

/-- This mutation keeps a sound guard service but lies about the source row's
return type. Guard soundness alone cannot justify declaration selection. -/
def erasedRange : Services Unit := { services with
  rows := fun world _ head arguments =>
    match PettaSourceTypeRows.lookup [] world head arguments with
    | .typed rows => .typed (rows.map fun row => { row with range := .sym "%Undefined%" })
    | other => other }

def stopped : Option (State Unit) :=
  match ((machine missingResult .eagerValue ordinary).run 1000 (initial missingResult ordinary)).2 with
  | .suspended _ saved => some saved
  | _ => none

def resumed : Option (List Atom × List Atom) := do
  let saved ← stopped
  observe services ordinary saved

def replayed : Option (List Atom × List Atom) := do
  let saved ← stopped
  let start := initial services ordinary
  observe services ordinary (start.1, {start.2 with world := {start.2.world with output := saved.2.world.output}})

theorem source_body_is_checked : Bridges.ScopedReturnFunction.checksHead ordinary "keep" 0 12 = true := by decide

theorem checked_entry_is_earned (operations : Services Unit) :
    PettaCallerReturnMachine.Invariant (fun _ : Unit => num 4) (initial operations ordinary) :=
  PettaCallerReturnEntry.checked_entry_invariant operations ordinary "keep" 0 12 source_body_is_checked
    control [num 4] (num 4) (.var "result") rfl rfl () [] (Allocator.empty 8 64) ⟨Effects.loaded ordinary, [], []⟩

theorem every_budget_keeps_the_actual_caller (operations : Services Unit) (fuel : Nat) (final : State Unit)
    (retained : PettaCallerReturnMachine.exitState
      ((machine operations .eagerValue ordinary).run fuel (initial operations ordinary)).2 = some final) :
    PettaCallerReturnMachine.Invariant (fun _ : Unit => num 4) final :=
  PettaCallerReturnMachine.run_retained_invariant (fun _ : Unit => num 4) operations ordinary fuel _
    (checked_entry_is_earned operations) final retained

def emptyProgram : SpaceSemantics.Program := {equations := [], declarations := []}
def syntheticControl : DControl := ⟨[], [], num 1, ∅, 0⟩
def syntheticFrame (depth : Nat) : CallFrame :=
  ⟨"prefix", ⟨[], .sym "Number"⟩, [], [], 0, [], [], .var "x", 0, num 1, depth, .body⟩

/-- This synthetic state has not been derived from source entry. Only the
frame depth changes between the two controls below. -/
def synthetic (depth : Nat) : State Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.empty, [], []⟩,
    [⟨[(syntheticControl, ⟨(), [syntheticFrame depth]⟩, [])], [], none⟩]⟩)

theorem synthetic_alias_view_holds_at_either_depth (depth : Nat) :
    PettaCallerReturnMachine.Invariant (fun _ : Unit => .var "x") (synthetic depth) := by
  refine ⟨.root _ _, ?_⟩
  change Bridges.ScopedReturnScopes.Stack (fun _ : Context Unit => .var "x")
    [PettaCallerReturnView.scope _]
  apply Bridges.ScopedReturnScopes.Stack.root
  intro item member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  cases List.mem_singleton.mp present
  apply (PettaCallerReturnView.work_iff (fun _ : Unit => .var "x") _).mpr
  apply PettaCallerReturnFrames.Frames.caller
  refine ⟨"x", ?_, .inl ?_⟩ <;> intro environment solved <;> rfl

theorem correct_depth_consumes_the_guard_before_publication :
    observe services emptyProgram (synthetic 1) = some ([.var "x"], []) := by cbv

theorem incorrect_depth_can_publish_the_inner_value :
    observe services emptyProgram (synthetic 2) = some ([num 1], []) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures

