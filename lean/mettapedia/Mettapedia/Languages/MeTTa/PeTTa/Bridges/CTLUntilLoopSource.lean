import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedLetSource

/-!
# The authored EU loop body

Each phase keeps the actual reached equations and older continuation.
Arithmetic binds the source let slot; named calls and the final conditional
use those bindings rather than substituted executable syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilSourceRows (number)

structure Names where
  formula : String
  operand : String
  current : String
  next : String
  count : String
  dropped : String
  result : String
  distinct : [formula, operand, current, next, count, dropped, result].Nodup

def app (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def increment (names : Names) : Atom := app "+" [.var names.current, number 1]
def roundCall (names : Names) : Atom := app "eu-round" [.var names.formula, .var names.operand, .var names.current, .var names.next]
def cleanupCall (names : Names) : Atom := app "drop" [.var names.formula, .var names.current]
def recurse (names : Names) : Atom := app "eu-loop" [.var names.formula, .var names.operand, .var names.next]
def branch (names : Names) : Atom := app "if" [app "==" [.var names.count, number 0], .var names.next, recurse names]
def afterRound (names : Names) : Atom := ScopedLetSource.source names.dropped (cleanupCall names) (branch names)
def afterIncrement (names : Names) : Atom := ScopedLetSource.source names.count (roundCall names) (afterRound names)
def nested (names : Names) : Atom := ScopedLetSource.source names.next (increment names) (afterIncrement names)
def body (names : Names) : Atom := app "let*" [.expression [
  .expression [.var names.next, increment names], .expression [.var names.count, roundCall names],
  .expression [.var names.dropped, cleanupCall names]], branch names]

def entry (caller : Control) (names : Names) : Control :=
  {caller with goals := .evaluate (body names) (.var names.result) :: caller.goals}
def incrementCaller (caller : Control) (names : Names) : Control :=
  ScopedLetSource.producerCaller caller names.next (increment names) (afterIncrement names) (.var names.result)
def incrementSlot (caller : Control) (names : Names) : String :=
  ScopedLetSource.slot caller names.next (increment names) (afterIncrement names) (.var names.result)
def incremented (caller : Control) (names : Names) (round : Nat) : Control :=
  ScopedAtomicPrimitive.returned (incrementCaller caller names) "+" [.var names.current, number 1]
    (.var (incrementSlot caller names)) (number (round + 1))

variable {Context Label : Type}

structure InitialFrame (codec : Codec Label) (label holds : Label) (round : Nat) (names : Names) (caller : Control) where
  principal : Environment
  resolved : resolve caller.bindings = some principal
  formula : read principal (.var names.formula) = codec.encode label
  operand : read principal (.var names.operand) = codec.encode holds
  current : read principal (.var names.current) = number round
  fresh : ∀ name ∈ [names.next, names.count, names.dropped, names.result], FreshFor name caller.bindings

theorem nested_expansion (names : Names) :
    Eval.nestedLets [.expression [.var names.next, increment names], .expression [.var names.count, roundCall names],
      .expression [.var names.dropped, cleanupCall names]] (branch names) = some (nested names) := rfl

theorem sequence_prefix (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) (names : Names) :
    (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (entry caller names) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (ScopedLetSource.entry caller names.next (increment names) (afterIncrement names) (.var names.result))
        context origins pending)) := by
  have step := ScopedQuerySource.sequence_entry .relational program allocator world
    {scope with frontier := (entry caller names, context, origins) :: pending} parents (entry caller names)
    context origins pending _ _ _ (.var names.result) caller.goals rfl rfl (nested_expansion names)
  have actual : (ScopedQuerySource.machine .relational program).step
      (placed allocator world scope parents (entry caller names) context origins pending) =
      some (.silent (placed allocator world scope parents
        (ScopedLetSource.entry caller names.next (increment names) (afterIncrement names) (.var names.result))
        context origins pending)) := by
    simpa only [placed, entry, nested, ScopedLetSource.entry] using step
  simp [Machine.run, actual]

theorem increment_prefix (codec : Codec Label) (label holds : Label) (round : Nat) (names : Names)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : InitialFrame codec label holds round names caller)
    (strict : ∀ index, index < 2 → Eval.argumentIsRaw program "+" index = false) :
    (ScopedQuerySource.machine .relational program).run 11
      (placed allocator world scope parents (entry caller names) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (incremented caller names round)
        context (origins ++ [0]) pending)) := by
  have first := sequence_prefix program allocator world scope parents caller context origins pending names
  have prepared := ScopedLetSource.preparation program allocator world scope parents caller context origins pending
    names.next (increment names) (afterIncrement names) (.var names.result) ⟨frame.principal, resolve_sound frame.resolved⟩
  obtain ⟨principal, representative, resolved, unbound⟩ := ScopedLetSource.producer_unbound caller names.next
    (increment names) (afterIncrement names) (.var names.result) frame.principal frame.resolved (frame.fresh _ (by simp))
  have inherited := ScopedLetSource.inherited caller names.next (increment names) (afterIncrement names) (.var names.result)
    principal (resolve_sound resolved)
  have current := CapturedQueryOperands.resolved_forces frame.resolved (.var names.current) (number round) frame.current
    (CTLUntilSourceCapture.number_closed round) principal inherited
  have one : read principal (number 1) = number 1 := CTLUntilSourceCapture.number_closed 1 principal
  have plus := ScopedAtomicPrimitive.source_prefix program allocator world scope parents (incrementCaller caller names)
    context origins pending "+" [.var names.current, number 1] (.var (incrementSlot caller names)) (number (round + 1))
    principal representative (by
      intro atom member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .variable _
      · exact .grounded _) (by decide) rfl rfl
    (by simp [callable, StdLib.known]) (by simpa using strict) resolved unbound
    (by
      intro atom member environment
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [current]; exact CTLUntilSourceCapture.number_closed round environment
      · rw [one]; exact CTLUntilSourceCapture.number_closed 1 environment)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [show [.var names.current, number 1].map (read principal) = [number round, number 1] by
        simp only [List.map_cons, List.map_nil, current, one]]
      simpa [number] using StdLib.integer_addition world.state (round : Int) 1)
    (CTLUntilSourceCapture.number_closed (round + 1))
  change (ScopedQuerySource.machine .relational program).run 7
    (placed allocator world scope parents
      (ScopedLetSource.producing caller names.next (increment names) (afterIncrement names) (.var names.result))
      context origins pending) =
    ([], .exhausted (placed allocator world scope parents (incremented caller names round) context (origins ++ [0]) pending)) at plus
  have firstFour := (ScopedQuerySource.machine .relational program).established_and_pending 1 3 _ _ [] first
  rw [prepared] at firstFour
  simp only [List.nil_append] at firstFour
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 4 7 _ _ [] firstFour
  rw [plus] at joined
  simpa only [List.nil_append] using joined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopSource
