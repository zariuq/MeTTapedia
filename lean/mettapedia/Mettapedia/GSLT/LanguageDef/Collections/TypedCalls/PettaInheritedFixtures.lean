import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures

/-!
# Source-reached body regions with older work and a real collection parent

The first authored call prints, commits its clause choice, and returns either
its Number argument or a wrong String. An older typed String call remains in
the host frontier. The nested variant starts that first call through collapse,
so its typed activation and inherited handoff genuinely occur at scope depth
two. Ready states below are obtained by running the actual named-call entry.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCheckpointFixtures (num text call)

def program (bad : Bool) : SpaceSemantics.Program where
  equations := [
    ⟨"keep", [.var "x"], call "let" [.var "printed", call "println!" [text "body"],
      call "let" [.var "committed", call "cut" [], if bad then text "wrong" else .var "x"]]⟩,
    ⟨"keep", [.var "x"], num 6⟩,
    ⟨"outside", [.var "value"], .var "value"⟩]
  declarations := [
    PettaSourceTypeRows.declaration "keep" (arrow [.sym "Number"] (.sym "Number")),
    PettaSourceTypeRows.declaration "outside" (arrow [.sym "Atom"] (.sym "String"))]
  layout := [.equation, .equation, .equation, .declaration, .declaration]

def services : Services Unit := PettaSourceTypeServices.services []

def initial (nested bad : Bool) : State Unit :=
  let first := call "keep" [num 4]
  let first := if nested then call "collapse" [first] else first
  let firstControl : DControl := ⟨[], [.evaluate first (.var "result")], .var "result", ∅, 9⟩
  let olderControl : DControl :=
    ⟨[], [.evaluate (call "outside" [text "outside"]) (.var "older")], .var "older", ∅, 0⟩
  (Allocator.empty 16 128,
    ⟨{state := Effects.loaded (program bad), output := [text "before"]},
      [⟨[(firstControl, ⟨(), []⟩, [0]), (olderControl, ⟨(), []⟩, [1])], [], none⟩]⟩)

def entryFuel (nested : Bool) : Nat := if nested then 7 else 6

def ready (nested bad : Bool) : Option (State Unit) :=
  match ((PettaOccurrenceOverlay.machine services .eagerValue (program bad)).run
      (entryFuel nested) (initial nested bad)).2 with
  | .exhausted reached => some reached
  | _ => none

theorem program_balanced (bad : Bool) : SpaceSemantics.Balanced (program bad) := by
  cases bad <;> simp [SpaceSemantics.Balanced, program]

theorem initial_frames_bounded (nested bad : Bool) : PettaFrameScopes.Bounded (initial nested bad) := by
  apply PettaFrameScopes.Scoped.root
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact PettaFrameScopes.CallsAt.empty _ ()

theorem ready_frames_bounded (nested bad : Bool) (reached : State Unit)
    (returned : ready nested bad = some reached) : PettaFrameScopes.Bounded reached := by
  have kept := PettaInheritedContext.actual_run_retained_bounds services (program bad)
    (entryFuel nested) (initial nested bad) (initial_frames_bounded nested bad)
  unfold ready at returned
  cases observed : ((PettaOccurrenceOverlay.machine services .eagerValue (program bad)).run
      (entryFuel nested) (initial nested bad)).2 with
  | exhausted final =>
      simp only [observed] at returned
      cases Option.some.inj returned
      exact kept reached (by simp only [observed, PettaCallerReturnMachine.exitState])
  | finished final | stuck final | suspended request final | faulted =>
      simp only [observed] at returned
      cases returned

def observe (result : PettaInheritedContext.HostResult Unit) : Option (List Atom × List Atom) :=
  match result.2 with
  | .finished final => some (result.1.map CollectedAnswer.value, final.2.world.output)
  | _ => none

def observed (nested bad : Bool) : Option (List Atom × List Atom) := do
  let reached ← ready nested bad
  observe (PettaInheritedContext.execute services (program bad) 120 (PettaInheritedContext.nest reached))

def withoutHandoff (nested bad : Bool) : Option (List Atom × List Atom) := do
  let reached ← ready nested bad
  let result := (PettaOccurrenceOverlay.machine (PettaInheritedContext.services services)
    .eagerValue (program bad)).run 120 (PettaInheritedContext.nest reached)
  observe (result.1, PettaInheritedContext.outcome result.2)

def readyView (nested bad : Bool) : Option (Nat × Nat × Bool × Bool) := do
  let reached ← ready nested bad
  let current ← reached.2.scopes.head?
  let (control, inside, _) ← current.frontier.head?
  let frame ← inside.calls.head?
  pure (reached.2.scopes.length, frame.scopeDepth, frame.phase == .body, !control.goals.isEmpty)

def zeroDelimiter (source : State Unit) : State Unit :=
  (source.1, {source.2 with scopes := match source.2.scopes with
    | [] => []
    | current :: parents => {current with frontier := match current.frontier with
        | [] => []
        | (control, inside, origins) :: pending => ({control with cutBoundary := 0}, inside, origins) :: pending} :: parents})

def wrongDelimiter : Option (List Atom × List Atom) := do
  let reached := (PettaOccurrenceOverlay.machine services .eagerValue (program false)).run 7 (initial false false)
  let reached ← match reached.2 with
    | .exhausted source => some source
    | _ => none
  observe (PettaInheritedContext.execute services (program false) 120 (PettaInheritedContext.nest (zeroDelimiter reached)))

def wrongDepth (source : State Unit) : State Unit :=
  (source.1, {source.2 with scopes := match source.2.scopes with
    | [] => []
    | current :: parents => {current with frontier := match current.frontier with
        | [] => []
        | (control, inside, origins) :: pending =>
            let inside := {inside with calls := match inside.calls with
              | [] => []
              | frame :: rest => {frame with scopeDepth := 1} :: rest}
            (control, inside, origins) :: pending} :: parents})

def unrebasedNested : Option (List Atom × List Atom) := do
  let reached ← ready true true
  observe (PettaInheritedContext.execute services (program true) 120 (PettaInheritedContext.nest (wrongDepth reached)))

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
