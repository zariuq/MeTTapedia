import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyCheckpoint

/-!
# A named typed call with one completed effect and a retained result guard

The actual full overlay starts at source evaluation of the named call.
Declarations and guard replies come from the loaded source world. Missing
result service is distinct from refusal. Resumption uses the saved state;
the replay mutation deliberately starts the call again.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def num (value : Int) : Atom := .grounded (.int value)
def text (value : String) : Atom := .grounded (.string value)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

def program (bad : Bool) : SpaceSemantics.Program where
  equations := [⟨"keep", [.var "x"], call "let" [.var "printed", call "println!" [text "body"],
    if bad then text "wrong" else .var "x"]⟩]
  declarations := [PettaSourceTypeRows.declaration "keep" (arrow [.sym "Number"] (.sym "Number"))]
  layout := [.equation, .declaration]

def services : Services Unit := PettaSourceTypeServices.services []

def initial (bad : Bool) : State Unit :=
  (Allocator.empty 8 64,
    ⟨{state := Effects.loaded (program bad), output := [text "before"]},
      [⟨[(⟨[], [.evaluate (call "keep" [num 4]) (.var "result")], .var "result", ∅, 9⟩, ⟨(), []⟩, [])], [], none⟩]⟩)

def observation (operations : Services Unit) (bad : Bool) (source : State Unit) :
    Option (List Atom × List Atom) :=
  let result := (PettaOccurrenceOverlay.machine operations .eagerValue (program bad)).run 100 source
  match result.2 with
  | .finished final => some (result.1.map CollectedAnswer.value, final.2.world.output)
  | _ => none

def missingResult : Services Unit := { services with
  orderedGuard := fun world index store expected value =>
    if index = 1 then none else PettaSourceTypeServices.orderedGuard [] world index store expected value
  guard_exact := by
    intro world index store expected value answers served
    by_cases missing : index = 1
    · simp [missing] at served
    · exact PettaSourceTypeServices.orderedGuard_exact [] world index store expected value answers
        (by simpa only [missing, if_false] using served) }

def erasedRange : Services Unit := { services with
  rows := fun world _ head arguments =>
    match PettaSourceTypeRows.lookup [] world head arguments with
    | .typed rows => .typed (rows.map fun row => {row with range := .sym "%Undefined%"})
    | other => other }

def suspended : Option (State Unit) :=
  match ((PettaOccurrenceOverlay.machine missingResult .eagerValue (program false)).run 100 (initial false)).2 with
  | .suspended (.guard "keep" 1 _ _) saved => some saved
  | _ => none

def resumed : Option (List Atom × List Atom) := do
  let saved ← suspended
  observation services false saved

def replayed : Option (List Atom × List Atom) := do
  let saved ← suspended
  let fresh := initial false
  observation services false (fresh.1, {fresh.2 with world := saved.2.world})

theorem good_head_is_source_checked :
    Bridges.ScopedReturnFunction.checksHead (program false) "keep" 0 12 = true := by decide

theorem wrong_return_recipe_is_rejected :
    Bridges.ScopedReturnFunction.checksHead (program true) "keep" 0 12 = false := by decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures
