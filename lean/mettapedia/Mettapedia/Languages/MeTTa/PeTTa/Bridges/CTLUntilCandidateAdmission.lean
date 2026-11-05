import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateBatchSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource

/-!
# Guarded EU candidates constructed from nested query frames

The frontier and edge captures append their actual row equations. Their
principal solver is constructed from the incoming caller, and preserves the
closed formula/round readings. Candidate syntax still contains the original
source variables; captured values are not substituted into executable code.

The two-capture algebra below does not erase or commute intervening query
preparation. Complete source composition must also retain its handle-slot
equations, as in `ScopedMatchPreparation` and the authored inner-query bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor)
open CTLUntilSourceRows (number)
open CTLUntilMixedStore (render Row)
open FlatQueryRowCodec (Codec)
open NamedGuardedCandidateBatch (Candidate State)

structure Names where
  formula : String
  nextRound : String
  next : String
  prior : String
  result : String
  temporary : String

def frontierBindings (caller : Control) (names : Names) (next : Nat) : Equations :=
  ScopedQuerySource.extend caller.bindings [(names.next, number next)]

def frame (caller : Control) (names : Names) (next prior : Nat) (older : List Goal) : Control :=
  {caller with
    bindings := ScopedQuerySource.extend (frontierBindings caller names next) [(names.prior, number prior)]
    goals := older}

theorem frame_inherited (caller : Control) (names : Names) (next prior : Nat) (older : List Goal)
    (environment : Environment) (solved : Solves environment (frame caller names next prior older).bindings) :
    Solves environment caller.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ (List.mem_append_left _ member))

/-- Actual query captures are consistent for every decoded pair of row
values. No successful source execution or selected post-frame is assumed. -/
theorem frame_resolves (caller : Control) (names : Names) (next prior : Nat) (older : List Goal)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (nextFresh : FreshFor names.next caller.bindings) (priorFresh : FreshFor names.prior caller.bindings)
    (apart : names.prior ≠ names.next) :
    ∃ final, resolve (frame caller names next prior older).bindings = some final := by
  obtain ⟨frontierPrincipal, frontierResolved⟩ := resolve_complete
    (CTLUntilSourceCapture.unbound_capture_consistent caller.bindings principal names.next names.next (number next)
      resolved (ClosedOnceQueryFrame.fresh_read _ _ principal nextFresh resolved) (CTLUntilSourceCapture.number_closed next))
  have stillFresh := CTLUntilSourceCapture.fresh_after_capture caller.bindings names.next names.prior next priorFresh apart
  exact resolve_complete (CTLUntilSourceCapture.unbound_capture_consistent _ frontierPrincipal names.prior names.prior
    (number prior) frontierResolved (ClosedOnceQueryFrame.fresh_read _ _ frontierPrincipal stillFresh frontierResolved)
    (CTLUntilSourceCapture.number_closed prior))

theorem frame_fresh (caller : Control) (names : Names) (next prior : Nat) (older : List Goal) (name : String)
    (fresh : FreshFor name caller.bindings) (apartNext : name ≠ names.next) (apartPrior : name ≠ names.prior) :
    FreshFor name (frame caller names next prior older).bindings :=
  CTLUntilSourceCapture.fresh_after_capture _ names.prior name prior
    (CTLUntilSourceCapture.fresh_after_capture caller.bindings names.next name next fresh apartNext) apartPrior

theorem frame_readings {Label : Type} (codec : Codec Label) (label : Label) (round next prior : Nat)
    (caller : Control) (names : Names) (older : List Goal) (before after : Environment)
    (beforeResolved : resolve caller.bindings = some before)
    (afterResolved : resolve (frame caller names next prior older).bindings = some after)
    (formulaRead : read before (.var names.formula) = codec.encode label)
    (roundRead : read before (.var names.nextRound) = number (round + 1)) :
    read after (.var names.formula) = codec.encode label ∧
      read after (.var names.nextRound) = number (round + 1) ∧ read after (.var names.prior) = number prior := by
  have inherited := frame_inherited caller names next prior older after (resolve_sound afterResolved)
  exact ⟨CapturedQueryOperands.resolved_forces beforeResolved _ _ formulaRead
      (LiteralQuerySource.read_literal _ (codec.literal label)) after inherited,
    CapturedQueryOperands.resolved_forces beforeResolved _ _ roundRead
      (CTLUntilSourceCapture.number_closed (round + 1)) after inherited,
    CTLUntilSourceCapture.captured_number_read (frontierBindings caller names next) names.prior prior after afterResolved⟩

def satisfactionCode (names : Names) : Atom :=
  .expression [.symbol "sat", .var names.formula, .var names.prior]

def frontierCode (names : Names) : Atom :=
  .expression [.symbol "fr", .var names.formula, .var names.nextRound, .var names.prior]

theorem payload_readings {Label : Type} (codec : Codec Label) (label : Label) (round prior : Nat)
    (names : Names) (principal : Environment)
    (formulaRead : read principal (.var names.formula) = codec.encode label)
    (roundRead : read principal (.var names.nextRound) = number (round + 1))
    (priorRead : read principal (.var names.prior) = number prior) :
    read principal (satisfactionCode names) = render codec (.satisfaction label prior) ∧
      read principal (frontierCode names) = render codec (.frontier label (round + 1) prior) := by
  simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at formulaRead roundRead priorRead
  simp only [satisfactionCode, frontierCode, read_eq_applyTypeValuation,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil,
    formulaRead, roundRead, priorRead, render]
  simp

def body (names : Names) (frontierHandle : NamedSpaces.Handle) : NamedGuardedInsertionSource.Body :=
  ⟨names.result, names.temporary, frontierHandle, satisfactionCode names, frontierCode names⟩

def candidate {Context Label : Type} (codec : Codec Label) (label : Label) (next prior : Nat)
    (satisfactionHandle frontierHandle : NamedSpaces.Handle) (caller : Control) (names : Names)
    (older : List Goal) (context : Context) (origins : List Nat) (frontierOccurrence edgeOccurrence : Nat) : Candidate Context := {
  caller := frame caller names next prior older
  context, origins := origins ++ [frontierOccurrence, edgeOccurrence]
  formulaName := names.formula, nodeName := names.prior
  request := CTLUntilPublicationSource.request codec satisfactionHandle label prior
  body := body names frontierHandle }

/-- The descriptor is exactly the control produced by the two captures and
the literal inner hit, including every inherited metadata field. -/
theorem capture_control {Context Label : Type} (codec : Codec Label) (label : Label) (next prior : Nat)
    (satisfactionHandle frontierHandle : NamedSpaces.Handle) (caller : Control) (names : Names)
    (older : List Goal) (context : Context) (origins : List Nat) (frontierOccurrence edgeOccurrence : Nat)
    (edgeBody satisfactionBody : Atom) :
    let chosen := candidate codec label next prior satisfactionHandle frontierHandle caller names older context origins frontierOccurrence edgeOccurrence
    ScopedQuerySource.bodyControl
      (ScopedQuerySource.bodyControl
        (ScopedQuerySource.bodyControl caller [(names.next, number next)] edgeBody (.var names.result) older)
        [(names.prior, number prior)] satisfactionBody (.var names.result) older)
      [] chosen.source (.var names.result) older = chosen.control := by
  simp only [ScopedQuerySource.bodyControl, ScopedQuerySource.extend, List.map_nil, List.append_nil,
    NamedGuardedCandidateBatch.Candidate.control, candidate, frame, frontierBindings, body]

/-- Both actual admission checkers accept every such captured candidate.
This is independent of graph shape, current membership and copy capacity. -/
theorem captured_admission {Context Label : Type} (codec : Codec Label) (label : Label) (round next prior : Nat)
    (satisfactionHandle frontierHandle : NamedSpaces.Handle) (caller : Control) (names : Names)
    (older : List Goal) (context : Context) (origins : List Nat) (frontierOccurrence edgeOccurrence : Nat)
    (program : SpaceSemantics.Program) (state : State Context) (pending : List (CollectionWork Context))
    (principal : Environment) (occurrence : Nat)
    (resolved : resolve caller.bindings = some principal)
    (formulaRead : read principal (.var names.formula) = codec.encode label)
    (roundRead : read principal (.var names.nextRound) = number (round + 1))
    (nextFresh : FreshFor names.next caller.bindings) (priorFresh : FreshFor names.prior caller.bindings)
    (resultFresh : FreshFor names.result caller.bindings) (temporaryFresh : FreshFor names.temporary caller.bindings)
    (distinct : [names.next, names.prior, names.result, names.temporary].Nodup)
    (row : program.equations[occurrence]? = some (NamedPresenceSource.declaration
      (CTLUntilPublicationSource.request codec satisfactionHandle label prior)))
    (otherHeads : ∀ index equation, program.equations[index]? = some equation → index ≠ occurrence → equation.head ≠ "in")
    (leftEvaluated : Eval.argumentIsRaw program "in" 0 = false)
    (rightEvaluated : Eval.argumentIsRaw program "in" 1 = false) :
    let chosen := candidate codec label next prior satisfactionHandle frontierHandle caller names older context origins frontierOccurrence edgeOccurrence
    let input := chosen.input program state pending
    ∃ guard receipt, NamedPresenceConditional.prepare input = some guard ∧
      NamedGuardedInsertionSource.prepare input guard chosen.body = some receipt ∧
        receipt.secondValue = render codec (.frontier label (round + 1) prior) := by
  dsimp only
  have distinctNames := distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinctNames
  obtain ⟨after, afterResolved⟩ := frame_resolves caller names next prior older principal resolved nextFresh priorFresh (by tauto)
  obtain ⟨formulaAfter, roundAfter, priorAfter⟩ := frame_readings codec label round next prior caller names older
    principal after resolved afterResolved formulaRead roundRead
  obtain ⟨firstRead, secondRead⟩ := payload_readings codec label round prior names after formulaAfter roundAfter priorAfter
  exact NamedGuardedInsertionAdmission.canonical_admission _ _ after (codec.encode label) (number prior)
    (render codec (.frontier label (round + 1) prior)) occurrence afterResolved formulaAfter priorAfter
    (codec.literal label) (.grounded _) rfl row otherHeads leftEvaluated rightEvaluated rfl rfl rfl
    (frame_fresh caller names next prior older names.temporary temporaryFresh (by tauto) (by tauto))
    (frame_fresh caller names next prior older names.result resultFresh (by tauto) (by tauto))
    (by tauto) firstRead secondRead (CTLUntilPublicationSource.frontier_literal codec label (round + 1) prior)
    (CTLUntilPublicationSource.satisfaction_ordinary codec label prior)
    (CTLUntilPublicationSource.frontier_ordinary codec label (round + 1) prior)

/-- Current decoded rows discharge the live guard-readiness condition.
No second-target availability or witness-copy capacity is assumed: those
failures remain source suspensions rather than admission handoff. -/
theorem decoded_not_reference {Context Label : Type} (codec : Codec Label) (label : Label) (node : Nat)
    (input : NamedPresenceConditional.Input Context) (body : NamedGuardedInsertionSource.Body)
    (guard : NamedPresenceConditional.Evidence input) (receipt : NamedGuardedInsertionSource.Evidence input guard body)
    (guardPrepared : NamedPresenceConditional.prepare input = some guard)
    (bodyPrepared : NamedGuardedInsertionSource.prepare input guard body = some receipt)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (pattern : input.request.pattern = render codec (.satisfaction label node))
    (atoms : List Atom) (rows : List (Row Label))
    (snapshot : input.world.state.read input.request.handle = some atoms)
    (decoded : CTLUntilMixedStore.decodeRows codec atoms = some rows) :
    (NamedGuardedCandidateExecution.execute input body).result ≠ .reference := by
  obtain ⟨actual, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  apply NamedGuardedCandidateExecution.execute_not_reference input body guard receipt guardPrepared bodyPrepared
    finished output atoms snapshot
  rw [← actual, pattern]
  exact CTLUntilMixedStore.rows_ready codec "sat" [codec.encode label, number node] (by simp) rows admitted

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateAdmission
