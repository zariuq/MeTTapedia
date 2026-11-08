import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPreparedReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDispatchDeopt

/-!
# Matched-only admission at the reached HE invocation

The caller has already selected a return policy and delivered its operands.
Equation dispatch now has three distinct observations: no equation matched,
an equation matched but produced no result, or matched producers returned
results. Only the first is a matched-only region's decline.

This factorization uses the actual hygienic query, emitted producer execution
and ordinary return receiver. Function-producing equations are included; their
bodies execute before the return receiver interprets each reached result.
There is no single-signature, closed-type or raw-argument self-delivery premise
at this boundary. Those belong to the preceding applicability stage.

The optional delivery below is an executable boundary extraction, not a model
of compiled equation bodies. Its soundness discharges the delivery premise of
the existing per-call deoptimization theorem. Native compilation, complete
source-query coverage and static return-classifier soundness remain separate.
The finite evaluator's exhausted approximation is not a proof of source absence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEMatchedReturnBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The delivered call and its retained return obligation. The depth is for
the remaining producer/return work, not a license to restart the source call. -/
structure Site where
  call : Atom
  expected : Atom
  bindings : Bindings
  depth : Nat
  live : List Atom

def Site.replies (site : Site) (space : Space) : ResultSet :=
  rawQueryResults space site.call site.expected site.bindings (site.depth + 1) site.live

/-- Equation occurrences produce emitted replies before the ordinary typed
return continuation. Physical duplicates and each producer's record survive. -/
def produced (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (reply : ResultPair) : ResultSet :=
  invocationResult space dispatch reply.1 reply.2 (site.depth + 1)
    (site.expected :: site.live) (some site.call)

def receive (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (reply : ResultPair) : ResultSet :=
  ordinaryCallReturn site.call reply.1 reply.2 fun value bindings =>
    evalAtom space dispatch value site.expected bindings (site.depth + 1) site.live

def equationReturns (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (replies : ResultSet) : ResultSet :=
  replies.flatMap fun reply => (produced space dispatch site reply).flatMap
    (receive space dispatch site)

/-- The reached invocation is an instance of the shared ordered boundary
algebra. Its work frames retain the selected range and caller record together
with each physical equation occurrence. -/
def equationBoundary (space : Space) (dispatch : GroundedDispatch) :
    Mettapedia.Machines.OrderedBoundary.Boundary Site (Site × ResultPair) ResultPair ResultPair where
  early site := if (site.replies space).isEmpty then [(site.call, site.bindings)] else []
  enter site := (site.replies space).map (site, ·)
  leave frame := receive space dispatch frame.1
  select := id

def equationWork (space : Space) (dispatch : GroundedDispatch)
    (frame : Site × ResultPair) : ResultSet := produced space dispatch frame.1 frame.2

theorem equationBoundary_run (space : Space) (dispatch : GroundedDispatch) (site : Site) :
    (equationBoundary space dispatch).run (equationWork space dispatch) site =
      if (site.replies space).isEmpty then [(site.call, site.bindings)]
      else equationReturns space dispatch site (site.replies space) := by
  simp only [Mettapedia.Machines.OrderedBoundary.Boundary.run, equationBoundary,
    List.flatMap_map, equationWork, id_eq]
  by_cases empty : site.replies space = []
  · simp [empty]
  · simp [List.isEmpty_eq_false_iff.mpr empty, equationReturns]

/-- Ownership is checked before this region reads any equation result. -/
def equationOwned (dispatch : GroundedDispatch) (call : Atom) : Bool :=
  match call with
  | .expression (operator :: _) =>
      !dispatch.isExecutable operator && !minimalInstruction call && !isErrorAtom call
  | _ => false

def offer (space : Space) (dispatch : GroundedDispatch) (site : Site) : Option ResultSet :=
  if equationOwned dispatch site.call then
    let replies := site.replies space
    if replies.isEmpty then none else some (equationReturns space dispatch site replies)
  else none

/-- The real invocation dispatcher factors through query occurrences,
producer completion and return processing. No plain-RHS premise is needed. -/
theorem invocation_factor {space : Space} {dispatch : GroundedDispatch} {site : Site}
    (owned : equationOwned dispatch site.call = true) (caller : Option Atom) :
    invoke space dispatch (.ordinary site.expected) site.call site.bindings
        (site.depth + 2) site.live caller =
      if (site.replies space).isEmpty then [(site.call, site.bindings)]
      else equationReturns space dispatch site (site.replies space) := by
  obtain ⟨call, expected, bindings, depth, live⟩ := site
  cases call with
  | symbol name => simp [equationOwned] at owned
  | var name => simp [equationOwned] at owned
  | grounded value => simp [equationOwned] at owned
  | expression items =>
      cases items with
      | nil => simp [equationOwned] at owned
      | cons operator arguments =>
          simp only [equationOwned, Bool.and_eq_true] at owned
          obtain ⟨⟨notExecutable', notInstruction'⟩, notError'⟩ := owned
          have notExecutable : dispatch.isExecutable operator = false := by simpa using notExecutable'
          have notInstruction : minimalInstruction (.expression (operator :: arguments)) = false := by
            simpa using notInstruction'
          have notError : isErrorAtom (.expression (operator :: arguments)) = false := by
            simpa using notError'
          rw [invoke]
          simp only [InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
            notExecutable, notInstruction, InvocationMode.expected, Site.replies]
          simp only [ordinaryCallReturn_notReducible]
          rfl

theorem equationBoundary_invocation {space : Space} {dispatch : GroundedDispatch} {site : Site}
    (owned : equationOwned dispatch site.call = true) (caller : Option Atom) :
    (equationBoundary space dispatch).run (equationWork space dispatch) site =
      invoke space dispatch (.ordinary site.expected) site.call site.bindings
        (site.depth + 2) site.live caller := by
  rw [equationBoundary_run, invocation_factor owned caller]

theorem offer_none_iff (space : Space) (dispatch : GroundedDispatch) (site : Site) :
    offer space dispatch site = none ↔
      equationOwned dispatch site.call = false ∨ site.replies space = [] := by
  unfold offer
  cases own : equationOwned dispatch site.call <;> simp

theorem offer_sound {space : Space} {dispatch : GroundedDispatch} {site : Site}
    {answers : ResultSet} (accepted : offer space dispatch site = some answers)
    (caller : Option Atom) :
    answers = invoke space dispatch (.ordinary site.expected) site.call site.bindings
      (site.depth + 2) site.live caller := by
  unfold offer at accepted
  split at accepted
  next owned =>
    dsimp only at accepted
    split at accepted
    next empty => simp at accepted
    next matched =>
      cases Option.some.inj accepted
      rw [invocation_factor owned caller, if_neg matched]
  next refused => simp at accepted

/-- Accepted empty output remains a completed execution. Whether an equation
matched is decided before its producer/body runs, never from final answers. -/
theorem accepted_has_query {space : Space} {dispatch : GroundedDispatch} {site : Site}
    {answers : ResultSet} (accepted : offer space dispatch site = some answers) :
    site.replies space ≠ [] := by
  intro empty
  have refused := (offer_none_iff space dispatch site).mpr (Or.inr empty)
  rw [accepted] at refused
  contradiction

/-- Every accepted output has both its equation occurrence and its reached
producer result as witnesses. No unmatched-call path is added to this branch. -/
theorem accepted_output_origin {space : Space} {dispatch : GroundedDispatch} {site : Site}
    {answers : ResultSet} (accepted : offer space dispatch site = some answers)
    {answer : ResultPair} (member : answer ∈ answers) :
    ∃ equationReply ∈ site.replies space,
      ∃ producerReply ∈ produced space dispatch site equationReply,
        answer ∈ receive space dispatch site producerReply := by
  unfold offer at accepted
  split at accepted
  · dsimp only at accepted
    split at accepted
    · simp at accepted
    · cases Option.some.inj accepted
      obtain ⟨equationReply, occurs, returned⟩ := List.mem_flatMap.mp member
      obtain ⟨producerReply, producedHere, received⟩ := List.mem_flatMap.mp returned
      exact ⟨equationReply, occurs, producerReply, producedHere, received⟩
  · simp at accepted

/-- A return analysis may omit the unmatched-call branch for this consumer.
Its remaining obligations concern actual producer/return paths, not raw RHS
syntax. In particular an emitted NotReducible can restore the ready call. -/
theorem matched_return_property {space : Space} {dispatch : GroundedDispatch} {site : Site}
    {answers : ResultSet} {property : ResultPair → Prop}
    (accepted : offer space dispatch site = some answers)
    (paths : ∀ equationReply ∈ site.replies space,
      ∀ producerReply ∈ produced space dispatch site equationReply,
      ∀ answer ∈ receive space dispatch site producerReply, property answer) :
    ∀ answer ∈ answers, property answer := by
  intro answer member
  obtain ⟨equationReply, occurs, producerReply, producedHere, received⟩ :=
    accepted_output_origin accepted member
  exact paths equationReply occurs producerReply producedHere answer received

/-- A concrete optional delivery supplies the existing tiering law's soundness
premise. Applicability is still on the original source arguments. -/
def prepared (space : Space) (dispatch : GroundedDispatch) (expected : Atom)
    (depth : Nat) (live : List Atom) (call : Atom) (bindings : Bindings) : Option ResultSet :=
  offer space dispatch ⟨call, expected, bindings, depth, live⟩

theorem prepared_sound (space : Space) (dispatch : GroundedDispatch) (expected : Atom)
    (depth : Nat) (live : List Atom) (call : Atom) (bindings : Bindings) (answers : ResultSet)
    (accepted : prepared space dispatch expected depth live call bindings = some answers) :
    answers = invoke space dispatch (.ordinary expected) call bindings (depth + 2) live :=
  offer_sound accepted none

theorem typed_source_delivery {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr bs)
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom) :
    HEReturns.keep (bs.flatMap fun b =>
      (interpretArgs space dispatch args params b (fuel + 1)
        (.symbol head :: callReturnType range :: live)).flatMap fun reply =>
          HEDispatchDeopt.tiered
            (fun call record => invoke space dispatch (.ordinary (callReturnType range))
              call record (fuel + 2) live)
            (prepared space dispatch (callReturnType range) fuel live)
            (HEDispatchDeopt.delivered head reply.1) reply.2) =
      evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings
        (fuel + 4) live :=
  HEDispatchDeopt.tiered_delivery declared ground notEmpty notError notAtom notExpression
    applicable enough live _ (prepared_sound space dispatch (callReturnType range) fuel live)

namespace Controls

open Mettapedia.Languages.MeTTa.HE.CompletedDelivery.Controls (equation)

def call : Atom := .expression [.symbol "partial", .grounded (.int 0)]
def other : Atom := .expression [.symbol "partial", .grounded (.int 1)]
def seven : Atom := .grounded (.int 7)
def block : Atom := .expression [.symbol "function", .expression [.symbol "return", seven]]
def source : Space := Space.ofList [equation call block, equation call block]
def site : Site := ⟨call, .symbol "Number", Bindings.empty, 28, []⟩

theorem function_producers_run_twice :
    offer source GroundedDispatch.none site =
      some [(seven, Bindings.empty), (seven, Bindings.empty)] := by decide +kernel

theorem function_producers_canonical :
    invoke source GroundedDispatch.none (.ordinary (.symbol "Number")) call Bindings.empty 30 =
      [(seven, Bindings.empty), (seven, Bindings.empty)] :=
  (offer_sound function_producers_run_twice none).symm

theorem partial_head_unmatched_declines :
    offer source GroundedDispatch.none {site with call := other} = none := by decide +kernel

theorem unmatched_canonical_keeps_call :
    invoke source GroundedDispatch.none (.ordinary (.symbol "Number")) other Bindings.empty 30 =
      [(other, Bindings.empty)] := by decide +kernel

def emptySource : Space := Space.ofList [equation call
  (.expression [.symbol "function", .expression [.symbol "superpose-bind", .expression []]])]

theorem matched_empty_does_not_decline :
    offer emptySource GroundedDispatch.none site = some [] := by decide +kernel

def refusalSource : Space := Space.ofList [equation call Atom.notReducible]

theorem matched_refusal_is_not_scalar :
    offer refusalSource GroundedDispatch.none site = some [(call, Bindings.empty)] := by decide +kernel

def bindingBlock : Atom := .expression [.symbol "function",
  .expression [.symbol "unify", seven, .var "local",
    .expression [.symbol "return", .var "local"], Atom.empty]]
def bindingSource : Space := Space.ofList [equation call bindingBlock]

/-- Producer execution creates a binding before returning; the delivery
retains it rather than rebuilding a result from the returned atom. -/
theorem nested_producer_bindings_retained :
    (offer bindingSource GroundedDispatch.none site).map
      (fun rows => rows.map fun reply => (reply.1, !reply.2.assignments.isEmpty)) =
        some [(seven, true)] := by decide +kernel

/-- A changed declaration or equation environment is not the only danger:
using the source call as fallback would repeat operand evaluation. This
boundary always retains the already-delivered call. -/
theorem different_ready_call_is_observable :
    invoke source GroundedDispatch.none (.ordinary (.symbol "Number")) call Bindings.empty 30 ≠
      invoke source GroundedDispatch.none (.ordinary (.symbol "Number")) other Bindings.empty 30 := by
  rw [function_producers_canonical, unmatched_canonical_keeps_call]
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEMatchedReturnBoundary
