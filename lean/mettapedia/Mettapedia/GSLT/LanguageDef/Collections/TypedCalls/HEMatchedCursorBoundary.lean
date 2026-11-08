import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEMatchedReturnBoundary

/-!
# The matched-occurrence flag at an HE prepared cursor boundary

The source query is the existing hygienic equation matcher, followed by its
actual caller-binding merge and cycle filter. The cursor groups those query
occurrences into batches and records a match before running the corresponding
producer. Exhaustion may therefore distinguish a matched producer with no
answers from a call with no matched equation.

The close policy follows the native prepared cursor's three unmatched modes.
In HE's reduce-to-self mode, a typed head hands off on no match; an untyped
head may deliver the call itself. The range-checked analyzer branch is a
typed branch, so its accepted executions need no unmatched-call provenance.
Its equation-return provenance remains an obligation: a matched producer can
emit NotReducible and restore a call-looking value.

These are the local scanner/close laws and their connection to reached HE
invocation. They do not certify the complete native matcher/compiler,
resource coverage, effects, or recursive return-provenance analyzer. Scanning
the finite executable query is not proof that a bounded source query was
complete; source coverage is a separate admission boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEMatchedCursorBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory (aliasConstraints)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HEMatchedReturnBoundary

/-- One actual query occurrence is merged with the reached caller before it
counts as a match. A failed merge or a cyclic candidate does not count. -/
def mergeOccurrence (site : Site) (reply : ResultPair) : ResultSet :=
  (mergeBindings reply.2 (aliasConstraints site.bindings) (site.depth + 1)).filterMap fun merged =>
    if merged.hasLoop then none else some (merged.applyFull reply.1 (site.depth + 1), merged)

def queryBatches (space : Space) (site : Site) : List ResultSet :=
  (queryEquationsAvoiding (equationScope site.live site.call site.expected site.bindings)
    space site.call (site.depth + 1)).map (mergeOccurrence site)

theorem queryBatches_flatten (space : Space) (site : Site) :
    (queryBatches space site).flatten = site.replies space := rfl

structure State where
  matched : Bool
  answers : ResultSet
  deriving DecidableEq

def initial : State := ⟨false, []⟩

/-- The matched flag depends on query occurrences, never on the producer's
final answer count. A checked scalar guard that rejects a body can thus
leave a matched call with no answers. -/
def acceptBatch (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (state : State) (batch : ResultSet) : State :=
  ⟨state.matched || !batch.isEmpty,
    state.answers ++ equationReturns space dispatch site batch⟩

def scan (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (batches : List ResultSet) (state : State := initial) : State :=
  batches.foldl (acceptBatch space dispatch site) state

theorem equationReturns_append (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (first later : ResultSet) :
    equationReturns space dispatch site (first ++ later) =
      equationReturns space dispatch site first ++ equationReturns space dispatch site later := by
  simp [equationReturns]

theorem scan_exact (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (batches : List ResultSet) (state : State) :
    scan space dispatch site batches state =
      ⟨state.matched || !batches.flatten.isEmpty,
        state.answers ++ equationReturns space dispatch site batches.flatten⟩ := by
  induction batches generalizing state with
  | nil => simp [scan, equationReturns]
  | cons batch batches ih =>
      simp only [scan, List.foldl_cons]
      rw [show batches.foldl (acceptBatch space dispatch site)
          (acceptBatch space dispatch site state batch) =
          scan space dispatch site batches (acceptBatch space dispatch site state batch) from rfl,
        ih]
      simp only [acceptBatch, List.flatten_cons, equationReturns_append, Bool.or_assoc,
        List.append_assoc, State.mk.injEq, and_true]
      cases batch <;> rfl

theorem actual_query_scan (space : Space) (dispatch : GroundedDispatch) (site : Site) :
    scan space dispatch site (queryBatches space site) =
      ⟨!(site.replies space).isEmpty,
        equationReturns space dispatch site (site.replies space)⟩ := by
  rw [scan_exact, queryBatches_flatten]
  rfl

theorem scan_split (space : Space) (dispatch : GroundedDispatch) (site : Site)
    (before later : List ResultSet) (state : State) :
    scan space dispatch site later (scan space dispatch site before state) =
      scan space dispatch site (before ++ later) state := by
  simp [scan, List.foldl_append]

inductive Unmatched where
  | fails
  | declines
  | self
  deriving DecidableEq

/-- The exact native close gate. Its arguments describe the current head,
not the root head or the producer's number of answers. -/
def declineNoMatch (policy : Unmatched) (declaresType takesArity : Bool) : Bool :=
  policy == .declines || (policy == .self && declaresType) ||
    (policy == .fails && !takesArity)

inductive Closure where
  | handoff
  | complete (answers : ResultSet)
  deriving DecidableEq

def close (policy : Unmatched) (declaresType takesArity : Bool) (site : Site)
    (state : State) : Closure :=
  if !state.matched && declineNoMatch policy declaresType takesArity then .handoff
  else if !state.matched && policy == .self then .complete (state.answers ++ [(site.call, site.bindings)])
  else .complete state.answers

/-- The source fact recorded by a compiled head's declares-type bit. -/
def declaresType (space : Space) (head : String) : Bool :=
  !(getAnnotatedTypes space (.symbol head)).isEmpty

/-- A selected function signature cannot originate from the unannotated
Undefined fallback. Thus typed applicability supplies the close gate's
declaration fact, without any extra assumption about result values. -/
theorem function_signature_declares {space : Space} {head : String} {signature : Atom}
    (present : signature ∈ getAtomTypes space (.symbol head))
    (function : isFunctionType signature = true) : declaresType space head = true := by
  unfold getAtomTypes at present
  dsimp only at present
  cases empty : (getAnnotatedTypes space (.symbol head)).isEmpty with
  | false => simp [declaresType, empty]
  | true =>
      simp only [empty, if_true, List.mem_singleton] at present
      subst signature
      simp [isFunctionType, Atom.undefinedType] at function

/-- Every declared HE head takes the unmatched handoff at this consumer.
No declaration's range need be rechecked to establish this control fact. -/
theorem typed_no_match_handoff (takesArity : Bool) (site : Site) (answers : ResultSet) :
    close .self true takesArity site ⟨false, answers⟩ = .handoff := by
  simp [close, declineNoMatch]

theorem typed_closed_iff_matched (takesArity : Bool) (site : Site) (state : State)
    (answers : ResultSet) :
    close .self true takesArity site state = .complete answers ↔
      state.matched = true ∧ answers = state.answers := by
  cases state with
  | mk matched returned => cases matched <;> simp [close, declineNoMatch, eq_comm]

/-- The local range-checked omission is about accepted execution only. It
does not turn the dialect's unmatched fallback into an empty answer. -/
theorem typed_scan_accepted_has_query (space : Space) (dispatch : GroundedDispatch)
    (site : Site) (takesArity : Bool) (answers : ResultSet)
    (accepted : close .self true takesArity site
      (scan space dispatch site (queryBatches space site)) = .complete answers) :
    site.replies space ≠ [] ∧
      answers = equationReturns space dispatch site (site.replies space) := by
  rw [actual_query_scan, typed_closed_iff_matched] at accepted
  exact ⟨by simpa using accepted.1, accepted.2⟩

/-- The native-style flag/close algorithm realizes the already proved
matched-only offer, rather than assuming compiled and canonical answers agree. -/
theorem typed_scan_eq_offer {space : Space} {dispatch : GroundedDispatch} (site : Site)
    (owned : equationOwned dispatch site.call = true) (takesArity : Bool) :
    (match close .self true takesArity site
      (scan space dispatch site (queryBatches space site)) with
     | .handoff => none
     | .complete answers => some answers) = offer space dispatch site := by
  rw [actual_query_scan]
  simp only [offer, owned, if_true]
  cases (site.replies space).isEmpty <;> simp [close, declineNoMatch]

theorem typed_scan_invocation {space : Space} {dispatch : GroundedDispatch} (site : Site)
    (owned : equationOwned dispatch site.call = true) (takesArity : Bool)
    (answers : ResultSet)
    (accepted : close .self true takesArity site
      (scan space dispatch site (queryBatches space site)) = .complete answers)
    (caller : Option Atom) :
    answers = invoke space dispatch (.ordinary site.expected) site.call site.bindings
      (site.depth + 2) site.live caller := by
  apply offer_sound (caller := caller)
  rw [← typed_scan_eq_offer site owned takesArity, accepted]

/-- The head-declaration condition is derived from the actual source typing
row used by the caller, rather than supplied as an unrelated Boolean. This
includes every range-checked selected signature, not only scalar ranges. -/
theorem selected_signature_scan_invocation {space : Space} {dispatch : GroundedDispatch}
    (site : Site) {head : String} {arguments : List Atom} {signature : Atom}
    (call : site.call = .expression (.symbol head :: arguments))
    (present : signature ∈ getAtomTypes space (.symbol head))
    (function : isFunctionType signature = true)
    (owned : equationOwned dispatch site.call = true) (takesArity : Bool)
    (answers : ResultSet)
    (accepted : close .self (declaresType space head) takesArity site
      (scan space dispatch site (queryBatches space site)) = .complete answers)
    (caller : Option Atom) :
    answers = invoke space dispatch (.ordinary site.expected)
      (.expression (.symbol head :: arguments)) site.bindings
      (site.depth + 2) site.live caller := by
  have declared := function_signature_declares present function
  rw [declared] at accepted
  simpa only [call] using typed_scan_invocation site owned takesArity answers accepted caller

/-- Every accepted output still arises through an equation producer and
ordinary return receiver. The unmatched COMPLETED alternative is absent;
COMPLETED-like results emitted by actual equations have not been erased. -/
theorem typed_scan_origin {space : Space} {dispatch : GroundedDispatch} (site : Site)
    (takesArity : Bool) (answers : ResultSet)
    (accepted : close .self true takesArity site
      (scan space dispatch site (queryBatches space site)) = .complete answers)
    (answer : ResultPair) (member : answer ∈ answers) :
    ∃ equationReply ∈ site.replies space,
      ∃ producerReply ∈ produced space dispatch site equationReply,
        answer ∈ receive space dispatch site producerReply := by
  obtain ⟨_, equality⟩ := typed_scan_accepted_has_query space dispatch site takesArity answers accepted
  rw [equality] at member
  obtain ⟨equationReply, occurs, returned⟩ := List.mem_flatMap.mp member
  obtain ⟨producerReply, made, received⟩ := List.mem_flatMap.mp returned
  exact ⟨equationReply, occurs, producerReply, made, received⟩

/-- Before exhaustion the scanner has no close event. In particular a zero
match count at a prefix cannot manufacture a handoff or a self answer. -/
def closeIfExhausted (remaining : List ResultSet) (policy : Unmatched)
    (declaresType takesArity : Bool) (site : Site) (state : State) : Option Closure :=
  if remaining.isEmpty then some (close policy declaresType takesArity site state) else none

theorem pending_is_not_closed (first : ResultSet) (rest : List ResultSet)
    (policy : Unmatched) (declaresType takesArity : Bool) (site : Site) (state : State) :
    closeIfExhausted (first :: rest) policy declaresType takesArity site state = none := rfl

namespace Controls

open HEMatchedReturnBoundary.Controls

def numberSignature : Atom := .expression [.symbol "->", .symbol "Number", .symbol "Number"]
def declaredSource : Space := source.add
  (.expression [.symbol ":", .symbol "partial", numberSignature])

theorem selected_function_supplies_close_gate :
    numberSignature ∈ getAtomTypes declaredSource (.symbol "partial") ∧
      isFunctionType numberSignature = true ∧ declaresType declaredSource "partial" = true := by
  decide +kernel

theorem unannotated_head_does_not_invent_declaration :
    declaresType source "partial" = false ∧
      numberSignature ∉ getAtomTypes source (.symbol "partial") := by decide +kernel

theorem duplicated_producers_close_with_both_occurrences :
    close .self true true site (scan source GroundedDispatch.none site (queryBatches source site)) =
      .complete [(seven, Bindings.empty), (seven, Bindings.empty)] := by decide +kernel

theorem matching_empty_producer_is_complete :
    close .self true true site
      (scan emptySource GroundedDispatch.none site (queryBatches emptySource site)) = .complete [] := by
  decide +kernel

theorem unmatched_typed_hands_off :
    close .self true true {site with call := other}
      (scan source GroundedDispatch.none {site with call := other}
        (queryBatches source {site with call := other})) = .handoff := by decide +kernel

theorem source_derived_typed_handoff :
    close .self (declaresType declaredSource "partial") true {site with call := other}
      (scan declaredSource GroundedDispatch.none {site with call := other}
        (queryBatches declaredSource {site with call := other})) = .handoff := by decide +kernel

theorem unmatched_untyped_restores_ready_call :
    close .self false true {site with call := other}
      (scan source GroundedDispatch.none {site with call := other}
        (queryBatches source {site with call := other})) = .complete [(other, Bindings.empty)] := by
  decide +kernel

theorem matched_refusal_remains_a_call_value :
    close .self true true site
      (scan refusalSource GroundedDispatch.none site (queryBatches refusalSource site)) =
        .complete [(call, Bindings.empty)] := by decide +kernel

theorem output_count_cannot_replace_match_flag :
    (scan emptySource GroundedDispatch.none site (queryBatches emptySource site)).answers = [] ∧
      (scan emptySource GroundedDispatch.none site (queryBatches emptySource site)).matched = true ∧
      close .self true true site ⟨false, []⟩ = .handoff := by decide +kernel

theorem a_pending_empty_batch_is_not_exhaustion :
    closeIfExhausted [[]] .self true true site initial = none ∧
      closeIfExhausted [] .self true true site initial = some .handoff := by decide +kernel

theorem fails_mode_preserves_arity_distinction :
    close .fails false true site initial = .complete [] ∧
      close .fails false false site initial = .handoff := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEMatchedCursorBoundary
