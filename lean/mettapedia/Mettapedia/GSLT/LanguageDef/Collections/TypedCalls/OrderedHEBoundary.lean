import Mettapedia.Machines.OrderedBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns
import Mettapedia.Languages.MeTTa.HE.LetChainResumption

/-!
# Ordered HE return boundaries and retained return obligations

The adapter factors the real HE interpreter theorem through an ordered
boundary. No list-to-bag quotient occurs in this correspondence. Producer
completion uses the existing saved-prefix/remaining-results machine.

A return frame retains the original call, instantiated range, bindings,
remaining evaluator fuel, and live-context list. The declaration space and
grounded dispatcher are fixed parameters of this return-stage model. It is
not yet an extraction or lifetime proof for a native cursor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedHEBoundary

open Mettapedia.Machines.OrderedBoundary
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

structure ReturnFrame where
  original : Atom
  range : Atom
  bindings : Bindings
  fuel : Nat
  live : List Atom

/-- Resume the ordinary return protocol at the range that the activation
actually owes, preserving its original error subject and binding frame. -/
def ReturnFrame.resume (space : Space) (dispatch_ : GroundedDispatch)
    (frame : ReturnFrame) (value : Atom) : ResultSet :=
  ordinaryCallReturn frame.original value frame.bindings fun value bindings =>
    evalAtom space dispatch_ value (callReturnType frame.range) bindings frame.fuel frame.live

def heReturns (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel : Nat) (live : List Atom) :
    Boundary ResultSet (ReturnFrame × Atom) Atom ResultPair where
  early := fun _ => []
  enter := fun replies => replies.map fun reply =>
    (⟨original, range, reply.2, fuel, live⟩, reply.1)
  leave := fun frame value => frame.1.resume space dispatch_ value
  select := HEReturns.keep

def rawReply (frame : ReturnFrame × Atom) : List Atom := [frame.2]

theorem he_return_run (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel : Nat) (live : List Atom) (replies : ResultSet) :
    (heReturns space dispatch_ original range fuel live).run rawReply replies =
      HEReturns.keep (replies.flatMap fun reply =>
        ordinaryCallReturn original reply.1 reply.2 fun value bindings =>
          evalAtom space dispatch_ value (callReturnType range) bindings fuel live) := by
  simp [Boundary.run, heReturns, rawReply, ReturnFrame.resume, List.flatMap_map]

/-- Exact ordered correspondence for the applicability profile of the
existing HE typed-call theorem. Empty replies and executable native heads
are not silently included in that profile. -/
theorem he_typed_call_boundary {space : Space} {dispatch_ : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch_.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch_ args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (.symbol head :: args)) (callReturnType range)
      bindings (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    (heReturns space dispatch_ (.expression (.symbol head :: args)) range (fuel + 1) live).run
        rawReply replies =
      evalAtom space dispatch_ (.expression (.symbol head :: args)) expected bindings
        (fuel + 4) live := by
  rw [he_return_run,
    HEReturns.typed_call_once declared ground notEmpty notError notExecutable notInstruction
      checked returns notAtom notExpression bindings enough arguments queried nonempty plain]

theorem keep_eq_completion (answers : ResultSet) :
    HEReturns.keep answers = ProducerCompletion.reference answers := by
  cases empty : (answers.filter fun reply => !isErrorAtom reply.1).isEmpty <;>
    simp [HEReturns.keep, ProducerCompletion.reference, empty]

/-- After return processing, selection is delayed until the complete ordered
batch is collected. Existing completion frames retain the exact prefix. -/
def completionFrame (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel : Nat) (live : List Atom) (replies : ResultSet) : ProducerCompletion.Frame :=
  ⟨[], replies.flatMap fun reply =>
    (ReturnFrame.mk original range reply.2 fuel live).resume space dispatch_ reply.1⟩

theorem completion_residual (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel : Nat) (live : List Atom) (replies : ResultSet) :
    ProducerCompletion.residual (completionFrame space dispatch_ original range fuel live replies) =
      (heReturns space dispatch_ original range fuel live).run rawReply replies := by
  rw [he_return_run, keep_eq_completion]
  rfl

/-- A partial administrative collection publishes nothing; a completed one
publishes the exact ordered HE boundary result. This budget is collection
work, not source-evaluator fuel. -/
theorem completion_run_preserves (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel budget : Nat) (live : List Atom) (replies : ResultSet) :
    match ProducerCompletion.run budget (completionFrame space dispatch_ original range fuel live replies) with
    | (some answers, none) =>
        answers = (heReturns space dispatch_ original range fuel live).run rawReply replies
    | (none, some next) =>
        ProducerCompletion.residual next =
          (heReturns space dispatch_ original range fuel live).run rawReply replies
    | _ => False := by
  have law := ProducerCompletion.run_preserves_completion budget
    (completionFrame space dispatch_ original range fuel live replies)
  rw [completion_residual] at law
  exact law

/-- The value projection of an ordered collector. Binding application and
opaque binding serialization are separate operations. -/
def collectValues (replies : ResultSet) : Atom := .expression (replies.map Prod.fst)

namespace Controls

def first : ResultPair := (.symbol "a", Bindings.empty)
def second : ResultPair := (.symbol "b", Bindings.empty)

def fault : ResultPair :=
  (.expression [.symbol "Error", .symbol "producer", .symbol "BadType"], Bindings.empty)

/-- Actual ordinary HE return processing at Atom retains ordered duplicate
values, while complete-batch selection suppresses the earlier error. -/
theorem ordered_atom_returns (space : Space) (dispatch_ : GroundedDispatch) :
    (heReturns space dispatch_ (.expression [.symbol "f"]) Atom.atomType 1 []).run rawReply
      [fault, first, first, second] = [first, first, second] := by
  rfl

/-- No partial error is published before the later successful alternatives
arrive; completion retains both duplicate occurrences in their order. -/
theorem completion_waits_for_later_success :
    ProducerCompletion.run 1 ⟨[], [fault, first, first, second]⟩ =
      (none, some ⟨[fault], [first, first, second]⟩) ∧
    ProducerCompletion.run 5 ⟨[], [fault, first, first, second]⟩ =
      (some [first, first, second], none) := by
  constructor <;> rfl

theorem same_bag_different_collection :
    (([first, second] : ResultSet) : Multiset ResultPair) = ([second, first] : ResultSet) ∧
      collectValues [first, second] ≠ collectValues [second, first] := by
  constructor <;> decide

/-- No observer of only the answer bag can reconstruct all ordered
collections. The forgotten order is not recoverable downstream. -/
theorem collection_does_not_factor_through_bag :
    ¬ ∃ collect : Multiset ResultPair → Atom, ∀ replies : ResultSet,
      collect replies = collectValues replies := by
  rintro ⟨collect, h⟩
  have same := congrArg collect same_bag_different_collection.1
  rw [h, h] at same
  exact same_bag_different_collection.2 same

def numberFrame : ReturnFrame :=
  ⟨.expression [.symbol "f"], .symbol "Number", Bindings.empty, 2, []⟩

def stringFrame : ReturnFrame := { numberFrame with range := .symbol "String" }

def forgetRange (frame : ReturnFrame) : Atom × Bindings × Nat × List Atom :=
  (frame.original, frame.bindings, frame.fuel, frame.live)

theorem number_frame_returns (space : Space) (dispatch_ : GroundedDispatch) :
    numberFrame.resume space dispatch_ (.grounded (.int 3)) =
      [(.grounded (.int 3), Bindings.empty)] := by
  unfold ReturnFrame.resume numberFrame
  rw [HEReturns.ordinaryCallReturn_grounded]
  exact (HEReturns.evalAtom_grounded (space := space) (dispatch := dispatch_) (.int 3)
    (type_ := .symbol "Number") rfl (by decide) (by decide) Bindings.empty
    (fuel := 1) (by decide) []).trans (by rfl)

theorem string_frame_rejects (space : Space) (dispatch_ : GroundedDispatch) :
    stringFrame.resume space dispatch_ (.grounded (.int 3)) =
      [(mkError (.grounded (.int 3)) (.badType (.symbol "String") (.symbol "Number")), Bindings.empty)] := by
  unfold ReturnFrame.resume stringFrame numberFrame
  rw [HEReturns.ordinaryCallReturn_grounded]
  exact (HEReturns.evalAtom_grounded (space := space) (dispatch := dispatch_) (.int 3)
    (type_ := .symbol "String") rfl (by decide) (by decide) Bindings.empty
    (fuel := 1) (by decide) []).trans (by rfl)

/-- The same value, original call, bindings, budget and live context can
resume differently solely because the retained return obligation differs. -/
theorem return_debt_is_observable (space : Space) (dispatch_ : GroundedDispatch) :
    forgetRange numberFrame = forgetRange stringFrame ∧
      numberFrame.resume space dispatch_ (.grounded (.int 3)) ≠
        stringFrame.resume space dispatch_ (.grounded (.int 3)) := by
  constructor
  · rfl
  · rw [number_frame_returns, string_frame_rejects]
    decide

theorem no_range_erased_resumption (space : Space) (dispatch_ : GroundedDispatch) :
    ¬ ∃ resume : (Atom × Bindings × Nat × List Atom) → Atom → ResultSet,
      ∀ frame value, resume (forgetRange frame) value = frame.resume space dispatch_ value := by
  rintro ⟨resume, h⟩
  have same := congrArg (fun f => resume f (.grounded (.int 3))) (return_debt_is_observable space dispatch_).1
  rw [h, h] at same
  exact (return_debt_is_observable space dispatch_).2 same

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedHEBoundary
