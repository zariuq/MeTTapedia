import Mettapedia.Languages.MeTTa.PeTTa.StreamingOnTheStep
import Mettapedia.Languages.MeTTa.PeTTa.StreamingDemand
import Mettapedia.Languages.MeTTa.PeTTa.StreamingCallerExtension
import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionReachability
import Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformReadsAtTheCall
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# PeTTa's streaming machine and the step, as an operational correspondence

`StreamingOnTheStep` proves that representation is a strong bisimulation between PeTTa's
streaming machine and the step restricted to the machine's rules. This module states that
result in the tree's notion of a correspondence between two systems
(`GSLT.Core.OperationalReadback`), so that it composes with any other correspondence by the
existing `comp`.

* `machineSystem`, `stepSystem`: the actual source states with their computed transitions,
  and the stores with the firings of the machine's rules, each as a system.
* `onTheStep`: the correspondence. A firing reads back as exactly one transition, and a
  transition is implemented by one firing.
* `related_exists`: every configuration of the machine has a store related to it.
* `hosted`: a language with a correspondence into PeTTa's machine has one into the step: the
  composite of the two.
* `reachable_world_iff`: a property of what every alternative shares (the answers so far, the
  effect world) is reachable in the machine exactly when it is reachable by firings, read off
  the store's world occurrence.
* `target_prefix_readback`, `target_prefix_state`: every independently supplied target
  prefix represents the actual runner's endpoint after exactly its number of firings.
* `advance_lifts`, `resume_after_target_prefix`: bounded execution and resumption keep the
  reached agenda, shared effects and binding packets; allowance is not completion.
* `pull_answer_fires`, `first_answer_lifts`: actual demand-provider executions compose with
  the store execution, including the effects of the returned packet's continuation.
* `written_match_read_then_run`: a read of selected occurrences and subsequent body
  evaluation form a run of real ordered store effects; the agenda retains each selected row's bindings.
* `afterFirstCommit_allRead`: the first-commit, all-read library route starts from that same
  retained state on ground rows with an unbound entry and one authored body.

Positive and negative examples: `Controls.published_answer` (an answer with no frame left is
published by one transition, and from a related store one firing reaches a store that shows
it) and `Controls.empty_agenda_no_step` (a configuration with an empty agenda has no
transition, and a store related to it has no firing).

The target uses the existing transition-indexed rule family, not a claimed finite compiler
or native implementation refinement. Source coverage is the independent streaming model's
coverage; this does not certify the whole SWI translator or a library's code protection.
`hosted` still takes a correspondence from another language as its argument. Checked whole
producer examples include effectful match, collection, literal code and a zero-divisor fault;
the over-protected-data control distinguishes a library integration defect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StreamingCorrespondence

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom matchAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (labels)
open DialectsAsStrategies.HEOnTheStep
open StreamingOnTheStep
open Unifying (Answer)
open Streaming (World Job State)
open Mettapedia.Machines.ProgressObservation (observePath)

universe uSource

/-- PeTTa's streaming machine as a system: its configurations and its transitions. -/
def machineSystem (registry : SpaceSemantics.Program) : GSLT :=
  equalityGSLT State (fun before after => Streaming.step registry before = some after)

/-- The step restricted to the machine's rules, as a system on stores. -/
def stepSystem (registry : SpaceSemantics.Program) : GSLT :=
  equalityGSLT (Store Shared PUnit Job Empty) (StoreStep (machine registry))

/-- **PeTTa's streaming machine on the step, as a correspondence.** A configuration is
related to the stores that represent it; every firing from such a store reads back as one
transition, and every transition is implemented by one firing. -/
def onTheStep (registry : SpaceSemantics.Program) :
    OperationalCorrespondence (machineSystem registry) (stepSystem registry) where
  related state store := Represents store (configOf state)
  readStep represented fired := .inr ((source_bisimulation registry).1 represented fired)
  forward represented transition := by
    obtain ⟨next, fired, representedNext⟩ :=
      (source_bisimulation registry).2 represented transition
    exact ⟨next, ⟨.cons ⟨fired⟩ (.refl next)⟩, representedNext⟩

/-- Every configuration has a store related to it. -/
theorem related_exists (registry : SpaceSemantics.Program)
    (state : State) : ∃ store, (onTheStep registry).related state store :=
  exists_represents (configOf state)

/-- **A language hosted on PeTTa's machine is hosted on the step.** The correspondence of the
language with the machine composes with the machine's correspondence with the step. -/
def hosted {source : GSLT.{uSource}} (registry : SpaceSemantics.Program)
    (onTheMachine : OperationalCorrespondence source (machineSystem registry)) :
    OperationalCorrespondence source (stepSystem registry) :=
  onTheMachine.comp (onTheStep registry)

/-- The composite relates a source term to a store through a configuration of the machine
that the store represents. -/
theorem hosted_related {source : GSLT.{uSource}} (registry : SpaceSemantics.Program)
    (onTheMachine : OperationalCorrespondence source (machineSystem registry))
    (term : source.Term) (store : Store Shared PUnit Job Empty) :
    (hosted registry onTheMachine).related term store ↔
      ∃ state, onTheMachine.related term state ∧ Represents store (configOf state) :=
  Iff.rfl

/-- The world of a represented store is the configuration's. -/
theorem world_of_represented {store : Store Shared PUnit Job Empty}
    {state : State} (represented : Represents store (configOf state)) :
    worldsOf (labels Prod.fst store.present) = {(configOf state).world} := by
  rw [represented.2, worldsOf_encode]

/-- **What every alternative shares is reachable in the machine exactly when it is reachable
by firings.** The property is read off the store's world occurrence. -/
theorem reachable_world_iff (registry : SpaceSemantics.Program) (holds : Shared → Prop)
    {state : State} {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf state)) :
    (∃ after, (machineSystem registry).MultiStep state after ∧ holds (configOf after).world) ↔
      ∃ final, (stepSystem registry).MultiStep store final ∧
        ∃ shared ∈ worldsOf (labels Prod.fst final.present), holds shared := by
  refine (onTheStep registry).reachable_iff (fun after => holds (configOf after).world)
    (fun final => ∃ shared ∈ worldsOf (labels Prod.fst final.present), holds shared)
    (fun {origin current} related => ?_) represented
  rw [world_of_represented related]
  simp

/-! ## Actual bounded runs and arbitrary implementation prefixes -/

/-- Every supplied implementation prefix reads back to the actual source
runner at exactly its number of firings. No administrative firing is erased. -/
theorem target_prefix_readback (registry : SpaceSemantics.Program)
    {state : State} {store final : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf state))
    (path : ExecutionPath (stepSystem registry) store final) :
    Represents final (configOf (Streaming.advance registry path.length state)) := by
  induction path generalizing state with
  | refl store => exact represented
  | cons fired rest ih =>
      obtain ⟨next, computed, nextRelated⟩ := (source_bisimulation registry).1 represented fired.down
      simpa only [Route.length, Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run,
        computed] using ih nextRelated

/-- All choices of physical occurrence identities give the same full source
endpoint for a fixed implementation-prefix length. -/
theorem target_prefix_state (registry : SpaceSemantics.Program)
    {state after : State} {store final : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf state))
    (path : ExecutionPath (stepSystem registry) store final)
    (finalRelated : Represents final (configOf after)) :
    after = Streaming.advance registry path.length state :=
  representation_unique finalRelated (target_prefix_readback registry represented path)

section ReturnCustody

open Streaming.Regions (WellFormed)
open Streaming.Regions.Custody (Address ledger live site transition_ledger issued_marker_stays_dead)
open LocatedSubstitution.Authority (Mark)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-- An actual implementation firing has the exact shared marker-ledger
effect of the source transition it represents. This is a control
projection, not a replacement of the firing's physical store effect. -/
theorem target_step_ledger {Request : Type*} [DecidableEq Request] (request : Request)
    (registry : SpaceSemantics.Program) {before : State} {store final : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before)) (good : WellFormed before)
    (fired : (stepSystem registry).Step store final) :
    ∃ after, Represents final (configOf after) ∧
      ∃ (picked : Selection (Address Request))
        (out : Vector (Mark (Address Request) Streaming.Regions.Boundary) picked.made.length),
        Enabled (fun _ : Address Request => ()) (live request before) (picked.commit (T := Unit)) ∧
        (ledger request before).Fresh picked ∧
        fire (live request before) (picked.commit (T := Unit)) = live request after ∧
        (ledger request before).advance (live request before) picked out = ledger request after := by
  obtain ⟨after, ran, related⟩ := (source_bisimulation registry).1 represented fired
  exact ⟨after, related, transition_ledger request ((Streaming.step_iff_transition _ _ _).mp ran) good⟩

/-- Retirement survives every represented implementation prefix, not
only a preferred schedule chosen by the source-to-target proof. -/
theorem target_prefix_retired_address_has_no_mark {Request : Type*} [DecidableEq Request]
    (request : Request) (registry : SpaceSemantics.Program)
    {before after : State} {store final : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (path : ExecutionPath (stepSystem registry) store final)
    (finalRelated : Represents final (configOf after)) (good : WellFormed before)
    {key : Nat} (issued : key < before.nextBoundary) (dead : site request key ∉ live request before) :
    (ledger request after).mark (site request key) = none := by
  rw [target_prefix_state registry represented path finalRelated]
  exact issued_marker_stays_dead request good (Streaming.advance_reachable registry path.length before) issued dead

end ReturnCustody

/-- Faults, completion and suspended work are read from the actual endpoint,
while answers retain their order and bindings. -/
theorem target_prefix_observations (registry : SpaceSemantics.Program)
    {state after : State} {store final : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf state))
    (path : ExecutionPath (stepSystem registry) store final)
    (finalRelated : Represents final (configOf after)) :
    Streaming.observe after = Streaming.run registry path.length state ∧
      Streaming.values after = Streaming.values (Streaming.advance registry path.length state) ∧
      after.world = (Streaming.advance registry path.length state).world := by
  rw [target_prefix_state registry represented path finalRelated]
  exact ⟨rfl, rfl, rfl⟩

/-- A route using the existing GSLT transition relation can recover a
physical firing at each of its edges, with the same endpoints and
count. Its proof did not retain a choice of rule instance. -/
theorem execution_path_has_firings (registry : SpaceSemantics.Program)
    {first last : Fired (machine registry)} (path : ExecutionPath (stepSystem registry) first last) :
    ∃ physical : Quiver.Path first last, physical.length = path.length := by
  induction path with
  | refl => exact ⟨.nil, rfl⟩
  | @cons before between after fired _ ih =>
    obtain ⟨rule, belongs, commit⟩ := fired.down
    obtain ⟨rest, paid⟩ := ih
    let first : Quiver.Path (V := Fired (machine registry)) before between :=
      Quiver.Path.cons .nil ⟨rule, belongs, commit⟩
    refine ⟨first.comp rest, ?_⟩
    have one : first.length = 1 := rfl
    rw [Quiver.Path.length_comp, one, paid]
    simp only [Route.length, Nat.add_comm 1]

/-- A fuel allowance executes at most that many firings. If the source stops
early the remaining allowance does not introduce extra target transitions. -/
theorem advance_lifts (registry : SpaceSemantics.Program) (fuel : Nat)
    {state : State} {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf state)) :
    ∃ final, ∃ path : ExecutionPath (stepSystem registry) store final,
      path.length ≤ fuel ∧ Represents final (configOf (Streaming.advance registry fuel state)) := by
  induction fuel generalizing state store with
  | zero => exact ⟨store, .refl store, Nat.le_refl _, represented⟩
  | succ fuel ih =>
      cases computed : Streaming.step registry state with
      | none =>
          refine ⟨store, .refl store, Nat.zero_le _, ?_⟩
          simpa only [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run, computed] using represented
      | some next =>
          obtain ⟨middle, fired, middleRelated⟩ := (source_bisimulation registry).2 represented computed
          obtain ⟨final, rest, bound, finalRelated⟩ := ih middleRelated
          refine ⟨final, .cons ⟨fired⟩ rest, Nat.succ_le_succ bound, ?_⟩
          simpa only [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run, computed] using finalRelated

/-- Continue the paid residual of an independently supplied target prefix;
the source expression is not re-entered against the reached world. -/
theorem resume_after_target_prefix (registry : SpaceSemantics.Program) (remaining : Nat)
    {state : State} {store current : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf state))
    (initialPath : ExecutionPath (stepSystem registry) store current) :
    ∃ final, ∃ suffix : ExecutionPath (stepSystem registry) current final,
      suffix.length ≤ remaining ∧
        Represents final (configOf (Streaming.advance registry (initialPath.length + remaining) state)) := by
  obtain ⟨final, suffix, bound, finalRelated⟩ := advance_lifts registry remaining
    (target_prefix_readback registry represented initialPath)
  exact ⟨final, suffix, bound, by simpa only [Streaming.advance_add] using finalRelated⟩

/-- A path of the independent source rules executes on the target from the
supplied represented state; it need not be reconstructed as a new request. -/
theorem source_path_lifts (registry : SpaceSemantics.Program)
    {before after : State} {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (path : Relation.ReflTransGen (Streaming.Transition registry) before after) :
    ∃ final, Nonempty (ExecutionPath (stepSystem registry) store final) ∧
      Represents final (configOf after) := by
  obtain ⟨fuel, endpoint⟩ := (Streaming.path_iff_advance registry before after).1 path
  obtain ⟨final, executed, _, finalRelated⟩ := advance_lifts registry fuel represented
  exact ⟨final, ⟨executed⟩, by simpa only [endpoint] using finalRelated⟩

/-- The first-answer provider's progress reply performs one actual firing. -/
theorem pull_progress_fires (registry : SpaceSemantics.Program)
    {before after : State} {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (progress : Streaming.pull registry before = (.progress, after)) :
    ∃ final, (stepSystem registry).Step store final ∧ Represents final (configOf after) :=
  (source_bisimulation registry).2 represented (Streaming.progress_transition progress).computed

/-- Publishing a provider answer is one firing and retains its paid residual. -/
theorem pull_answer_fires (registry : SpaceSemantics.Program)
    {before after : State} {answer : Answer} {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (answered : Streaming.pull registry before = (.answer answer, after)) :
    ∃ final, (stepSystem registry).Step store final ∧ Represents final (configOf after) :=
  (source_bisimulation registry).2 represented (Streaming.answer_transition answered).computed

/-- The common demand client's actual producer prefix, including the returned
answer's effects and pending alternatives, has a target execution. -/
theorem first_answer_lifts (registry : SpaceSemantics.Program)
    {before ready after : State} {count : Nat} {answer : Answer}
    {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (progress : Mettapedia.Machines.StoreAndDemand.FirstAnswer.Progress
      (Streaming.pull registry) before count ready)
    (answered : Streaming.pull registry ready = (.answer answer, after)) :
    ∃ final, Nonempty (ExecutionPath (stepSystem registry) store final) ∧
      Represents final (configOf after) :=
  source_path_lifts registry represented (Streaming.paid_first_answer_reachable progress answered)

/-- Lift the actual delimiter cut and read it back from every target
prefix of the prescribed length. The outer continuation has not run. -/
theorem once_cut_lifts (registry : SpaceSemantics.Program)
    {before ready after : State} {count : Nat} {answer : Answer}
    {bindings : Subst} {expression : Atom} {caller : List Streaming.Frame} {older : List Job}
    {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (entry : before.agenda = .execute
      ⟨.evaluate bindings (.expression [.symbol "once",expression]),caller⟩ :: older)
    (good : Streaming.Regions.WellFormed before)
    (progress : Mettapedia.Machines.StoreAndDemand.FirstAnswer.Progress
      (Streaming.pull registry)
      (Streaming.CallerExtension.firstBody before (.evaluate bindings expression)) count ready)
    (answered : Streaming.pull registry ready = (.answer answer,after)) :
    let cut := {after with agenda := .execute ⟨.returned [answer],caller⟩ :: older, answers := before.answers}
    (∃ final, ∃ path : ExecutionPath (stepSystem registry) store final,
      path.length ≤ count + 2 ∧ Represents final (configOf cut)) ∧
    ∀ final (path : ExecutionPath (stepSystem registry) store final), path.length = count + 2 →
      Represents final (configOf cut) := by
  dsimp only
  have exactCut := Streaming.CallerExtension.once_answer_exact entry good progress answered
  constructor
  · obtain ⟨final,path,steps,reached⟩ := advance_lifts registry (count + 2) represented
    rw [exactCut] at reached
    exact ⟨final,path,steps,reached⟩
  · intro final path paid
    have reached := target_prefix_readback registry represented path
    rwa [paid,exactCut] at reached

section TemplateExecution

open Interface
open Streaming (Frame)
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaQueryInterpretation (scan continuations joinedRequest)
open PeTTaStoreSelection (atomFrames)
open RunsAsFirings (Supply Tracks)
open Unifying (queryJoin queryLegs joinedBodies)

/-! ## The occurrence read and its actual source continuation -/

private def queueBodies (before : State) (examined : Nat) (bodies : List Unifying.Control)
    (caller : List Frame) (pending : List Job) : State :=
  { before with
    world := { before.world with uses := before.world.uses + examined }
    agenda := .execute ⟨.sequence bodies [], caller⟩ :: pending }

/-- Keep each joined binding with the original template. Every attempted
row of each reached leg consumes its own renaming use. -/
def resumeMatch {O : Type} (before : State) (examined : Nat) (body : Atom)
    (packets : List (List O × Subst)) (caller : List Frame) (pending : List Job) : State :=
  queueBodies before examined (joinedBodies body packets) caller pending

variable {O : Type} {supply : Supply O}

/-- One written match return performs the admitted snapshot read and places
its bodies on the actual agenda, ahead of pending location answers. -/
theorem written_match_handoff {registry : SpaceSemantics.Program} {before : State} {ids : List O}
    (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {more : List Answer} {pattern body : Atom}
    {caller : List Frame} {pending : List Job} {handle : NamedSpaces.Handle}
    {rows : List Atom} {packets : List (List O × Subst)} {used : Nat}
    (agenda : before.agenda =
      .execute ⟨.returned (answer :: more), .source (.query pattern body) :: caller⟩ :: pending)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (prepared : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      answer.bindings before.world.uses = some (packets,used)) :
    let after := resumeMatch before used body packets caller
      (Streaming.laterAnswers more (.source (.query pattern body) :: caller) pending)
    Streaming.Transition registry before after ∧
      RunsAsFirings.askStream supply registry ids before = some (joinedRequest packets) := by
  dsimp only
  have sourceMove := RunsAsFirings.written_match_continues (registry := registry)
    (source := before.world.configuration (.returned [answer]) [.query pattern body])
    tracks rfl rfl resolved opened prepared
  constructor
  · exact .answer agenda (.source sourceMove (.plain rfl))
  · have nextQuery := RunsAsFirings.Asked.writtenMatch (S := supply)
      (registry := registry) (ids := ids)
      (source := before.world.configuration (.returned [answer]) [.query pattern body])
      rfl rfl resolved opened prepared
    have request := RunsAsFirings.ask_of_asked nextQuery
    simpa only [RunsAsFirings.askStream, RunsAsFirings.source?, agenda, Streaming.phaseControl,
      Bool.false_eq_true, ↓reduceIte, Option.bind_some] using request

open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom) in
/-- Reuse packets prepared in an older ground view when the read's ordered
hits and charge are preserved. The resulting evaluator step uses the
live caller, world, and allocation supply. -/
theorem written_match_reuses_ground_capture {registry : SpaceSemantics.Program}
    {before : State} {ids : List O} (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {more : List Answer} {pattern body : Atom} {caller : List Frame}
    {pending : List Job} {handle : NamedSpaces.Handle} {rows : List Atom}
    {packets : List (List O × Subst)} {used oldUse : Nat} (old : List O)
    (agenda : before.agenda =
      .execute ⟨.returned (answer :: more), .source (.query pattern body) :: caller⟩ :: pending)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (saved : queryJoin supply.label old (queryLegs pattern) answer.bindings oldUse = some (packets,used))
    (width : old.length = (supply.rowsAt handle ids).length)
    (oldGround : ∀ row ∈ old, isGroundAtom (supply.label row) = true)
    (newGround : ∀ row ∈ supply.rowsAt handle ids, isGroundAtom (supply.label row) = true)
    (screen : ∀ leg ∈ queryLegs pattern, ∀ bindings, Unifying.GroundRange bindings →
      Unifying.groundHits supply.label old bindings leg =
        Unifying.groundHits supply.label (supply.rowsAt handle ids) bindings leg)
    (range : Unifying.GroundRange answer.bindings) :
    let after := resumeMatch before used body packets caller
      (Streaming.laterAnswers more (.source (.query pattern body) :: caller) pending)
    Streaming.Transition registry before after ∧
      RunsAsFirings.askStream supply registry ids before = some (joinedRequest packets) := by
  have reusable := Unifying.queryJoin_ground_reuse supply.label old (supply.rowsAt handle ids)
    width oldGround newGround (queryLegs pattern) screen answer.bindings range oldUse before.world.uses
  exact written_match_handoff tracks agenda resolved opened (reusable.symm.trans saved)

variable [DecidableEq O] in
/-- Composing the read with real execution preserves the reached shared
world, ordered answers, faults and any pending suffix. The first read is
counted once; later template writes do not reopen it. -/
theorem written_match_read_then_run {registry : SpaceSemantics.Program} {before : State} {ids : List O}
    (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {more : List Answer} {pattern body : Atom}
    {caller : List Frame} {pending : List Job} {handle : NamedSpaces.Handle}
    {rows : List Atom} {packets : List (List O × Subst)} {used : Nat}
    (agenda : before.agenda =
      .execute ⟨.returned (answer :: more), .source (.query pattern body) :: caller⟩ :: pending)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (prepared : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      answer.bindings before.world.uses = some (packets,used))
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge)
    (fuel : Nat) :
    let view := resumeMatch before used body packets caller
      (Streaming.laterAnswers more (.source (.query pattern body) :: caller) pending)
    Streaming.advance registry (fuel + 1) before = Streaming.advance registry fuel view ∧
      ∃ run : (OrderedStore.step atomFrames PUnit.unit supply.label).Run (knowledge, ids),
        run.word.map (fun firing => (firing.2 : OrderedStore.Publication Atom O)) =
          joinedRequest packets :: RunsAsFirings.requests supply registry fuel view ids ∧
        run.last.1 = knowledge ∧
        Tracks supply run.last.2 (Streaming.advance registry fuel view).world.state := by
  dsimp only
  obtain ⟨moved, asked⟩ := written_match_handoff (registry := registry) tracks agenda resolved opened prepared
  have computed := moved.computed
  have unchanged : OrderedStore.publish ids (joinedRequest packets).selection = ids :=
    OrderedStore.reads_only ids (packets.flatMap Prod.fst)
  have advanced := Mettapedia.Machines.BoundedDeterministicRun.run.eq_2
    (Streaming.step registry) before fuel
  simp only [computed] at advanced
  obtain ⟨run, receipt, kept, aligned⟩ :=
    RunsAsFirings.streaming_store_run (S := supply) registry knowledge consistent (fuel + 1) before ids tracks
  refine ⟨advanced, run, ?_, kept, ?_⟩
  · simpa only [RunsAsFirings.requests, computed, asked, unchanged] using receipt
  · unfold Streaming.advance
    rw [← advanced]
    exact aligned

/-- An implementation may prepare the written match by pulling a cursor on
the retained entry view. Finishing certifies the original complete capture,
including its exact freshening charge. Cursor transitions are not source fuel;
pending cursor packets do not yet license this atomic handoff. -/
theorem written_match_cursor_read_then_run [DecidableEq O]
    {registry : SpaceSemantics.Program} {before : State} {ids : List O}
    (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {more : List Answer} {pattern body : Atom}
    {caller : List Frame} {pending : List Job} {handle : NamedSpaces.Handle}
    {rows : List Atom} {packets : List (List O × Subst)} {last cursorFuel : Nat}
    (agenda : before.agenda =
      .execute ⟨.returned (answer :: more), .source (.query pattern body) :: caller⟩ :: pending)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (drained : (PeTTaQueryInterpretation.JoinCursor.machine supply.label).run cursorFuel
      (PeTTaQueryInterpretation.JoinCursor.start (supply.rowsAt handle ids) (queryLegs pattern)
        answer.bindings before.world.uses) = (packets, .finished last))
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge)
    (fuel : Nat) :
    let view := resumeMatch before (last - before.world.uses) body packets caller
      (Streaming.laterAnswers more (.source (.query pattern body) :: caller) pending)
    Streaming.advance registry (fuel + 1) before = Streaming.advance registry fuel view ∧
      ∃ run : (OrderedStore.step atomFrames PUnit.unit supply.label).Run (knowledge, ids),
        run.word.map (fun firing => (firing.2 : OrderedStore.Publication Atom O)) =
          joinedRequest packets :: RunsAsFirings.requests supply registry fuel view ids ∧
        run.last.1 = knowledge ∧
        Tracks supply run.last.2 (Streaming.advance registry fuel view).world.state :=
  written_match_read_then_run tracks agenda resolved opened
    (PeTTaQueryInterpretation.JoinCursor.finished_exact _ _ _ _ _ _ drained) knowledge consistent fuel

open Streaming.CallerExtension (sequencePrefix sequence_prefix_cut_exact)
open Mettapedia.Machines.StoreAndDemand

/-- The demanded prefix begins at the same world and renaming supply as
the complete source capture. It deliberately has no older alternatives. -/
def matchBodyPrefix (before : State) (used : Nat) (body : Atom) (packets : List (List O × Subst)) :
    State :=
  sequencePrefix {before with world := {before.world with uses := before.world.uses + used}}
    (joinedBodies body packets)

/-- If the completed capture has this ordered prefix, a first answer
earned by that prefix determines the actual query cut. Unexecuted query
body packets and pending location answers are cut; older callers remain. -/
theorem written_match_prefix_cut_exact {registry : SpaceSemantics.Program}
    {before ready after : State} {ids : List O} (tracks : Tracks supply ids before.world.state)
    {location : Answer} {more : List Answer} {pattern body : Atom} {handle : NamedSpaces.Handle}
    {caller : List Frame} {pending older : List Job} {rows : List Atom}
    {earlier later : List (List O × Subst)} {used count key : Nat} {answer : Answer}
    (agenda : before.agenda = .execute
      ⟨.returned (location :: more), .source (.query pattern body) :: .first key :: caller⟩ ::
        (pending ++ .first key :: older))
    (good : Streaming.Regions.WellFormed before)
    (resolved : Effects.readHandle location.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (prepared : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      location.bindings before.world.uses = some (earlier ++ later, used))
    (progress : FirstAnswer.Progress (Streaming.pull registry)
      (matchBodyPrefix before used body earlier) count ready)
    (answered : Streaming.pull registry ready = (.answer answer, after)) :
    Streaming.advance registry (count + 3) before =
      {after with agenda := .execute ⟨.returned [answer],caller⟩ :: older, answers := before.answers} := by
  let caller' := .first key :: caller
  let frames := .source (.query pattern body) :: caller'
  let unread := Streaming.laterAnswers more frames pending
  let handed := resumeMatch before used body (earlier ++ later) caller'
    (Streaming.laterAnswers more frames (pending ++ .first key :: older))
  have moved : Streaming.Transition registry before handed :=
    (written_match_handoff tracks agenda resolved opened prepared).1
  have entered : Streaming.advance registry 1 before = handed := by
    simp only [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run.eq_2,
      Mettapedia.Machines.BoundedDeterministicRun.run.eq_1, moved.computed]
  have valid := Streaming.Regions.advance_wellFormed registry 1 before good
  rw [entered] at valid
  have readTail : Streaming.laterAnswers more frames (pending ++ .first key :: older) =
      unread ++ .first key :: older := by cases more <;> rfl
  have preparedAgenda : handed.agenda = .execute
      ⟨.sequence (joinedBodies body earlier ++ joinedBodies body later) [], caller'⟩ ::
        (unread ++ .first key :: older) := by
    simp only [handed, resumeMatch, queueBodies, readTail, joinedBodies, List.map_append]
  have paid := sequence_prefix_cut_exact (before := handed) preparedAgenda valid
    (show FirstAnswer.Progress (Streaming.pull registry) (sequencePrefix handed (joinedBodies body earlier))
      count ready from progress) answered
  rw [show count + 3 = 1 + (count + 2) by omega, Streaming.advance_add, entered]
  exact paid

/-- A partial cursor may license the observed first answer only together
with the completed-capture certificate and the actual paid source body.
The administrative read budget is separate from the source step count. -/
theorem written_match_cursor_prefix_cut {registry : SpaceSemantics.Program}
    {before ready after : State} {ids : List O} (tracks : Tracks supply ids before.world.state)
    {location : Answer} {more : List Answer} {pattern body : Atom} {handle : NamedSpaces.Handle}
    {caller : List Frame} {pending older : List Job} {rows : List Atom}
    {earlier all : List (List O × Subst)} {used count key cursorFuel : Nat} {answer : Answer}
    {saved : PeTTaQueryInterpretation.JoinCursor.State O}
    (agenda : before.agenda = .execute
      ⟨.returned (location :: more), .source (.query pattern body) :: .first key :: caller⟩ ::
        (pending ++ .first key :: older))
    (good : Streaming.Regions.WellFormed before)
    (resolved : Effects.readHandle location.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (complete : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      location.bindings before.world.uses = some (all, used))
    (paused : (PeTTaQueryInterpretation.JoinCursor.machine supply.label).run cursorFuel
      (PeTTaQueryInterpretation.JoinCursor.start (supply.rowsAt handle ids) (queryLegs pattern)
        location.bindings before.world.uses) = (earlier, .exhausted saved))
    (progress : FirstAnswer.Progress (Streaming.pull registry)
      (matchBodyPrefix before used body earlier) count ready)
    (answered : Streaming.pull registry ready = (.answer answer, after)) :
    let cut := {after with agenda := .execute ⟨.returned [answer],caller⟩ :: older, answers := before.answers}
    Streaming.advance registry (count + 3) before = cut ∧
    ∀ store, Represents store (configOf before) →
      (∃ final, ∃ path : ExecutionPath (stepSystem registry) store final,
        path.length ≤ count + 3 ∧ Represents final (configOf cut)) ∧
      ∀ final (path : ExecutionPath (stepSystem registry) store final),
        path.length = count + 3 → Represents final (configOf cut) := by
  dsimp only
  obtain ⟨later, rfl, _⟩ :=
    PeTTaQueryInterpretation.JoinCursor.paused_prefix_of_completed supply.label _ _ _ _ _ complete paused
  have exactCut := written_match_prefix_cut_exact tracks agenda good resolved opened complete progress answered
  refine ⟨exactCut, ?_⟩
  intro store represented
  constructor
  · obtain ⟨final, path, paid, reaches⟩ := advance_lifts registry (count + 3) represented
    rw [exactCut] at reaches
    exact ⟨final, path, paid, reaches⟩
  · intro final path paid
    have reaches := target_prefix_readback registry represented path
    rwa [paid, exactCut] at reaches

/-- A fault in capture invalidates its packets for the atomic source
handoff. Even an already discovered path cannot turn a failed capture
into either a running template or a completed negative query. -/
theorem written_match_failed_cursor_interrupts {registry : SpaceSemantics.Program}
    {before : State} {ids : List O} (tracks : Tracks supply ids before.world.state)
    {location : Answer} {more : List Answer} {pattern body : Atom} {handle : NamedSpaces.Handle}
    {caller : List Frame} {older : List Job} {rows : List Atom}
    {earlier : List (List O × Subst)} {cursorFuel : Nat}
    (agenda : before.agenda = .execute
      ⟨.returned (location :: more), .source (.query pattern body) :: caller⟩ :: older)
    (resolved : Effects.readHandle location.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (failed : (PeTTaQueryInterpretation.JoinCursor.machine supply.label).run cursorFuel
      (PeTTaQueryInterpretation.JoinCursor.start (supply.rowsAt handle ids) (queryLegs pattern)
        location.bindings before.world.uses) = (earlier, .faulted)) :
    Streaming.pull registry before = (.interrupted, before) ∧
      ∀ fuel, Streaming.observe (Streaming.advance registry fuel before) = .suspended before := by
  have readback := PeTTaQueryInterpretation.JoinCursor.run_exact supply.label cursorFuel
    (PeTTaQueryInterpretation.JoinCursor.start (supply.rowsAt handle ids) (queryLegs pattern)
      location.bindings before.world.uses)
  rw [failed, PeTTaQueryInterpretation.JoinCursor.remaining_start] at readback
  have incomplete : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      location.bindings before.world.uses = none := by
    cases h : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
        location.bindings before.world.uses <;>
      simp [PeTTaQueryInterpretation.JoinCursor.reconstruct, h] at readback ⊢
  apply Streaming.query_capture_interrupted agenda
  have sameRows := tracks.rows handle rows opened
  have located : (Effects.readHandle location.value >>= before.world.state.read) = some rows := by
    simp [resolved, opened]
  simp [Unifying.queries, located, sameRows, Unifying.queryBatch_from_join, incomplete]

/-- Any first target firing at this represented match handoff reaches the
same captured agenda, and resumption on the target runs its real bodies. -/
theorem written_match_target_prefix {registry : SpaceSemantics.Program}
    {before : State} {ids : List O} (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {more : List Answer} {pattern body : Atom}
    {caller : List Frame} {pending : List Job} {handle : NamedSpaces.Handle}
    {rows : List Atom} {packets : List (List O × Subst)} {used : Nat}
    (agenda : before.agenda =
      .execute ⟨.returned (answer :: more), .source (.query pattern body) :: caller⟩ :: pending)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : before.world.state.read handle = some rows)
    (prepared : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      answer.bindings before.world.uses = some (packets,used))
    {store middle : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf before))
    (fired : (stepSystem registry).Step store middle) (fuel : Nat) :
    let view := resumeMatch before used body packets caller
      (Streaming.laterAnswers more (.source (.query pattern body) :: caller) pending)
    Represents middle (configOf view) ∧
      ∃ final, ∃ path : ExecutionPath (stepSystem registry) middle final,
        path.length ≤ fuel ∧ Represents final (configOf (Streaming.advance registry fuel view)) := by
  dsimp only
  have moved := (written_match_handoff (registry := registry) tracks agenda resolved opened prepared).1
  obtain ⟨after, actual, related⟩ := (source_bisimulation registry).1 represented fired
  rw [moved.computed] at actual
  cases actual
  exact ⟨related, advance_lifts registry fuel related⟩

/-! ## Commit first, then run the original templates -/

/-- The split is a property of the authored template, not of a substituted
value. Carry the binding environment to each body without rewriting its
syntax: PeTTa itself decides which positions demand evaluation. -/
def templateControls (template : Atom) (bindings : Subst) : List Unifying.Control :=
  (LibTransform.split template).map (Unifying.Control.evaluate bindings)

/-- The first-commit caller route of the ordered one-sided library model.
The scoped evaluator consumes its jobs. It reserves the original row view's
range of use numbers and starts bodies only after the commit. Failed
validation and a successful answerless commit yield different receipts. -/
def afterFirstCommit (before : State) (handle : NamedSpaces.Handle) (sources : LibTransform.Sources)
    (template : Atom) (caller : List Frame) (pending : List Job) : Except Effects.Fault (Option State) :=
  match before.world.state.read handle with
  | none => .error .invalidSpace
  | some rows =>
      match LibTransform.fireFirst rows sources (templateControls template) with
      | none => .ok none
      | some (committed, bodies) =>
          let updated := if committed = rows then some before.world.state
            else before.world.state.write handle committed
          match updated with
          | none => .error .invalidSpace
          | some world =>
              .ok (some (queueBodies { before with world := { before.world with state := world } }
                rows.length bodies caller pending))

/-- The committed view affects precisely the selected space. Its entire
batch of bodies is installed, including an empty batch. -/
theorem afterFirstCommit_reads_back {before : State} {handle : NamedSpaces.Handle}
    {sources : LibTransform.Sources} {template : Atom} {rows committed : List Atom}
    {bodies : List Unifying.Control} (caller : List Frame) (pending : List Job)
    (opened : before.world.state.read handle = some rows)
    (fired : LibTransform.fireFirst rows sources (templateControls template) = some (committed, bodies)) :
    ∃ after, afterFirstCommit before handle sources template caller pending = .ok (some after) ∧
      after.world.state.read handle = some committed ∧
      (∀ other, other ≠ handle → after.world.state.read other = before.world.state.read other) ∧
      after.agenda = .execute ⟨.sequence bodies [], caller⟩ :: pending := by
  by_cases untouched : committed = rows
  · subst committed
    refine ⟨queueBodies before rows.length bodies caller pending, ?_, opened, fun _ _ => rfl, rfl⟩
    simp only [afterFirstCommit, opened, fired, if_true]
  · obtain ⟨world, written⟩ :=
      NamedSpaces.Store.write_exists_of_read_some _ _ _ committed opened
    refine ⟨queueBodies { before with world := { before.world with state := world } }
        rows.length bodies caller pending, ?_, ?_, ?_, rfl⟩
    · simp only [afterFirstCommit, opened, fired, if_neg untouched, written]
    · exact NamedSpaces.Store.write_reads_back _ _ _ _ written
    · exact fun other distinct => NamedSpaces.Store.write_read_other _ _ other _ _ written distinct

theorem fireFirst_allRead_matches_query (rows : List Atom) (pattern body : Atom) (use : Nat)
    (ground : ∀ row ∈ rows, isGroundAtom row = true)
    (oneBody : LibTransform.split body = [body]) :
    LibTransform.fireFirst rows (LibTransformStep.allRead pattern) (templateControls body) =
      (Unifying.queryBodies [] pattern body use rows).map (fun bodies => (rows, bodies)) := by
  rw [LibTransformStep.fireFirst_all_read,
    Unifying.queryBodies_ground (fun _ absent => (List.not_mem_nil absent).elim) use rows ground]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and, templateControls, oneBody,
    List.map_cons, List.map_nil]
  clear ground
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [LibTransform.matchesIn, List.filterMap_cons] at ih ⊢
      cases matchAtom [] pattern row <;> simp [ih]

/-- On ground rows and an unbound read entry, the library's all-read plan
installs exactly the actual written match continuation. This is equality of
the full retained state, so any amount of actual body execution agrees. -/
theorem afterFirstCommit_allRead {before : State} {ids : List O}
    (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {handle : NamedSpaces.Handle} {rows : List Atom}
    {pattern body : Atom} {packets : List (O × Subst)} (caller : List Frame) (pending : List Job)
    (unbound : answer.bindings = []) (opened : before.world.state.read handle = some rows)
    (ground : ∀ row ∈ rows, isGroundAtom row = true) (oneBody : LibTransform.split body = [body])
    (prepared : scan supply.label answer.bindings pattern before.world.uses
      (supply.rowsAt handle ids) = some packets) :
    afterFirstCommit before handle (LibTransformStep.allRead pattern) body caller pending =
      .ok (some (resumeMatch before (supply.rowsAt handle ids).length body
        (packets.map fun (origin,bound) => ([origin],bound)) caller pending)) := by
  have labelRows := tracks.rows handle rows opened
  have scanned := PeTTaQueryInterpretation.scan_source supply.label answer.bindings pattern body
    before.world.uses (supply.rowsAt handle ids)
  rw [← labelRows, prepared, Option.map_some, unbound] at scanned
  have examined : rows.length = (supply.rowsAt handle ids).length := by rw [labelRows, List.length_map]
  simp only [afterFirstCommit, opened,
    fireFirst_allRead_matches_query rows pattern body before.world.uses ground oneBody,
    scanned, Option.map_some, if_true, examined, resumeMatch, joinedBodies,
    continuations, List.map_map, Function.comp_def]

/-- Ground snapshot matching needs no supplied selection witness. Its
library handoff and the real written match step compute the same state,
before any of the retained bodies runs. -/
theorem allRead_and_written_match_same_step {registry : SpaceSemantics.Program}
    {before : State} {ids : List O} (tracks : Tracks supply ids before.world.state)
    {answer : Answer} {more : List Answer} {pattern body : Atom} {handle : NamedSpaces.Handle}
    {rows : List Atom} {caller : List Frame} {pending : List Job}
    (agenda : before.agenda =
      .execute ⟨.returned (answer :: more), .source (.query pattern body) :: caller⟩ :: pending)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : before.world.state.read handle = some rows) (unbound : answer.bindings = [])
    (atomic : queryLegs pattern = [pattern])
    (ground : ∀ row ∈ rows, isGroundAtom row = true) (oneBody : LibTransform.split body = [body]) :
    ∃ reached, Streaming.step registry before = some reached ∧
      afterFirstCommit before handle (LibTransformStep.allRead pattern) body caller
        (Streaming.laterAnswers more (.source (.query pattern body) :: caller) pending) =
          .ok (some reached) := by
  have actual := Unifying.queryBodies_ground (pattern := pattern) (body := body)
    (fun _ absent : _ => (List.not_mem_nil absent).elim) before.world.uses rows ground
  have projection := PeTTaQueryInterpretation.scan_source supply.label answer.bindings pattern body
    before.world.uses (supply.rowsAt handle ids)
  rw [← tracks.rows handle rows opened, unbound, actual] at projection
  obtain ⟨packets, prepared, _⟩ := Option.map_eq_some_iff.mp projection.symm
  rw [← unbound] at prepared
  have joined : queryJoin supply.label (supply.rowsAt handle ids) (queryLegs pattern)
      answer.bindings before.world.uses =
        some (packets.map fun (origin,bound) => ([origin],bound), (supply.rowsAt handle ids).length) := by
    rw [atomic, Unifying.queryJoin_singleton]
    change (scan supply.label answer.bindings pattern before.world.uses (supply.rowsAt handle ids)).map _ = _
    rw [prepared]
    rfl
  have returned := written_match_handoff (registry := registry) tracks agenda resolved opened joined
  exact ⟨_, returned.1.computed, afterFirstCommit_allRead tracks caller _ unbound opened ground oneBody prepared⟩

end TemplateExecution

namespace Controls

/-- The configuration of a machine state. -/
abbrev at_ (world : World) (agenda : List Job) (answers : List Answer) :
    State := ⟨world, agenda, answers, 0⟩

/-- Positive: an answer with no frame left is published by one transition. -/
theorem publishes (registry : SpaceSemantics.Program) (world : World) (answer : Answer) :
    (machineSystem registry).Step (at_ world [.execute ⟨.returned [answer], []⟩] [])
      (at_ world [] [answer]) :=
  rfl

/-- Positive: from a store related to that configuration, firings reach a store whose world
shows the published answer. -/
theorem published_answer (registry : SpaceSemantics.Program) (world : World) (answer : Answer)
    {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (at_ world [.execute ⟨.returned [answer], []⟩] []))) :
    ∃ final, (stepSystem registry).MultiStep store final ∧
      ∃ shared ∈ worldsOf (labels Prod.fst final.present), shared.answers = [answer] :=
  (reachable_world_iff registry (fun shared => shared.answers = [answer]) represented).1
    ⟨at_ world [] [answer], .step (publishes registry world answer) (.refl _), rfl⟩

/-- Negative: a configuration with an empty agenda has no transition. -/
theorem empty_agenda_no_transition (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) (next : State) :
    ¬ (machineSystem registry).Step (at_ world [] answers) next := by
  intro step
  cases step

/-- Negative: a store related to a configuration with an empty agenda has no firing. -/
theorem empty_agenda_no_step (registry : SpaceSemantics.Program) (world : World)
    (answers : List Answer) {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (at_ world [] answers)))
    (next : Store Shared PUnit Job Empty) :
    ¬ (stepSystem registry).Step store next := by
  intro fired
  obtain ⟨after, computed, _⟩ := (source_bisimulation registry).1 represented fired
  exact empty_agenda_no_transition registry world answers after computed

def emptyRegistry : SpaceSemantics.Program := { equations := [], declarations := [] }
def emptyWorld : World := { state := Effects.empty }
def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def choices : Atom := .expression [.symbol "superpose", .expression [a, b, a]]
def collected : Atom := .expression [.symbol "collapse", choices]
def emptyCollected : Atom := .expression [.symbol "collapse", .expression [.symbol "empty"]]
def quotedComputation : Atom := .expression [.symbol "quote",
  .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]]

theorem source_choices_keep_duplicates :
    Streaming.values (Streaming.advance emptyRegistry 30 (Streaming.enter emptyWorld choices)) = [a, b, a] := by
  decide +kernel

theorem source_collection_is_one_answer :
    Streaming.values (Streaming.advance emptyRegistry 30 (Streaming.enter emptyWorld collected)) =
      [.expression [a, b, a]] := by
  decide +kernel

theorem source_empty_collection_is_not_no_answer :
    Streaming.values (Streaming.advance emptyRegistry 30 (Streaming.enter emptyWorld emptyCollected)) =
      [.expression []] := by
  decide +kernel

theorem source_quote_does_not_run_arithmetic :
    Streaming.values (Streaming.advance emptyRegistry 10 (Streaming.enter emptyWorld quotedComputation)) =
      [.expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]] := by
  decide +kernel

private def callerDemandRegistry (held : Bool) : SpaceSemantics.Program :=
  { equations := [⟨"demand-consumer", [.var "argument"], .symbol "done"⟩]
    declarations := [.expression [.symbol ":", .symbol "demand-consumer",
      .expression [.symbol "->", .symbol (if held then "Atom" else "%Undefined%"), .symbol "Atom"]]]
    layout := [.equation, .declaration] }

private def callerDemandFact : Atom := .expression [.symbol "demand-witness", .symbol "payload"]

private def callerDemandStart (held : Bool) : State :=
  Streaming.enter {state := Effects.loaded (callerDemandRegistry held)}
    (.expression [.symbol "demand-consumer",
      .expression [.symbol "add-atom", .symbol "&self", callerDemandFact]])

/-- The written call selects argument demand from its declaration. The
held operand is never run; the strict operand writes before the shared
authored clause returns its constant result. -/
theorem authored_argument_demand_observation (held : Bool) :
    let registry := callerDemandRegistry held
    let after := Streaming.advance registry 88 (callerDemandStart held)
    after.agenda = [] ∧ Streaming.values after = [.symbol "done"] ∧
      after.world.state.core =
        SpaceSemantics.loadedAtoms registry ++ (if held then [] else [callerDemandFact]) := by
  cases held <;> decide +kernel

theorem authored_argument_demand_on_the_step (held : Bool) {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (callerDemandStart held))) :
    let registry := callerDemandRegistry held
    ∃ final, ∃ path : ExecutionPath (stepSystem registry) store final,
      path.length ≤ 88 ∧ ∀ reached : State, Represents final (configOf reached) →
        reached.agenda = [] ∧ Streaming.values reached = [.symbol "done"] ∧
          reached.world.state.core =
            SpaceSemantics.loadedAtoms registry ++ (if held then [] else [callerDemandFact]) := by
  dsimp only
  obtain ⟨final, path, bound, finished⟩ := advance_lifts (callerDemandRegistry held) 88 represented
  refine ⟨final, path, bound, fun reached reads => ?_⟩
  rw [representation_unique reads finished]
  exact authored_argument_demand_observation held

def seed (value : Atom) : Atom := .expression [.symbol "seed", value]
def seen (value : Atom) : Atom := .expression [.symbol "seen", value]
def effectWorld : World := { state := NamedSpaces.Store.new [seed a, seed b] [] }
def effectfulMatch : Atom := .expression [.symbol "match", .symbol "&self", seed (.var "x"),
  .expression [.symbol "add-atom", .symbol "&self", seen (.var "x")]]

/-- A whole producer runs both of its differently bound continuations. -/
theorem source_effectful_match :
    let reached := Streaming.advance emptyRegistry 60 (Streaming.enter effectWorld effectfulMatch)
    reached.agenda = [] ∧ Streaming.values reached = [Effects.boolean true, Effects.boolean true] ∧
      reached.world.state.core = [seed a, seed b, seen a, seen b] := by
  decide +kernel

def overProtectedMatch : Atom := .expression [.symbol "match", .symbol "&self", seed (.var "x"),
  .expression [.symbol "add-atom", .symbol "&self", seen (.expression [.symbol "quote", .var "x"])]]

/-- Quoting below an Atom-demand argument changes stored data; it is not an
evaluation barrier that can be inserted indiscriminately into a template. -/
theorem protecting_stored_data_changes_the_effect :
    let ordinary := Streaming.advance emptyRegistry 60 (Streaming.enter effectWorld effectfulMatch)
    let wrapped := Streaming.advance emptyRegistry 60 (Streaming.enter effectWorld overProtectedMatch)
    wrapped.agenda = [] ∧
      wrapped.world.state.core = [seed a, seed b,
        seen (.expression [.symbol "quote", a]), seen (.expression [.symbol "quote", b])] ∧
      wrapped.world.state.core ≠ ordinary.world.state.core := by
  decide +kernel

theorem effectful_match_has_complete_target_execution {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (Streaming.enter effectWorld effectfulMatch))) :
    ∃ final, ∃ path : ExecutionPath (stepSystem emptyRegistry) store final,
      path.length ≤ 60 ∧ ∀ after : State, Represents final (configOf after) →
        after.agenda = [] ∧ Streaming.values after = [Effects.boolean true, Effects.boolean true] ∧
          after.world.state.core = [seed a, seed b, seen a, seen b] := by
  obtain ⟨final, path, bound, finalRelated⟩ := advance_lifts emptyRegistry 60 represented
  refine ⟨final, path, bound, ?_⟩
  intro after related
  rw [representation_unique related finalRelated]
  exact source_effectful_match

/-- Each effectful template publishes its own packet. Reading the
physical firing path reports both true results, even though they
have equal values, and preserves both writes in the reached world. -/
theorem effectful_match_firing_word_keeps_duplicates {store : Fired (machine emptyRegistry)}
    (represented : Represents store (configOf (Streaming.enter effectWorld effectfulMatch))) :
    ∃ (final : Fired (machine emptyRegistry)) (path : Quiver.Path store final),
      path.length ≤ 60 ∧
      (observePath (streamedAnswer emptyRegistry) path).map
        (fun answer => Unifying.resolve answer.bindings answer.value) =
        [Effects.boolean true, Effects.boolean true] ∧
      ∃ after : State, Represents final (configOf after) ∧
        after.agenda = [] ∧ after.world.state.core = [seed a, seed b, seen a, seen b] := by
  obtain ⟨final, planned, within, representedFinished⟩ := advance_lifts emptyRegistry 60 represented
  obtain ⟨path, count⟩ := execution_path_has_firings emptyRegistry planned
  obtain ⟨reached, exactWord⟩ := firing_path_reads_stream emptyRegistry represented path
  have same := representation_unique reached representedFinished
  have published := source_effectful_match
  rw [same] at exactWord reached
  refine ⟨final, path, count.trans_le within, ?_, _, reached, published.1, published.2.2⟩
  have empty : (Streaming.enter effectWorld effectfulMatch).answers = [] := rfl
  rw [empty, List.nil_append] at exactWord
  rw [← exactWord]
  exact published.2.1

private def coreView (world : World) : List Atom := world.state.core

private def eraseCut (entry : List Atom × Option Answer) : List Atom × Option Atom :=
  (entry.1, entry.2.map (fun answer => Unifying.resolve answer.bindings answer.value))

/-- Each publication follows the write of its own template on the
actual streaming path. Equal answer values do not collapse the two
packets or move the second write before the first packet. -/
theorem effectful_match_fires_in_world_and_answer_order {store : Fired (machine emptyRegistry)}
    (represented : Represents store (configOf (Streaming.enter effectWorld effectfulMatch))) :
    ∃ (last : Fired (machine emptyRegistry)) (path : Quiver.Path store last),
      path.length ≤ 60 ∧
      (observePath (streamedWorld emptyRegistry coreView) path).map eraseCut =
        [([seed a, seed b, seen a], none), ([seed a, seed b, seen a], some (Effects.boolean true)),
          ([seed a, seed b, seen a, seen b], none),
          ([seed a, seed b, seen a, seen b], some (Effects.boolean true))] ∧
      Represents last (configOf (Streaming.advance emptyRegistry 60 (Streaming.enter effectWorld effectfulMatch))) := by
  obtain ⟨last, path, within, reached, word⟩ := advance_world_stream_lifts emptyRegistry coreView 60 represented
  refine ⟨last, path, within, ?_, reached⟩
  rw [word]
  decide +kernel

private def restoreAfterWrite : Atom := .expression [.symbol "let", .var "added",
  .expression [.symbol "add-atom", .symbol "&self", seen a],
  .expression [.symbol "let", .var "removed", .expression [.symbol "remove-atom", .symbol "&self", seen a],
    .symbol "done"]]

/-- Reading only final values and visible store contents cannot detect
an intervening insert/remove pair. Both computations and both observed
histories are executions of the actual PeTTa machine on the step. -/
theorem write_and_restore_is_not_silent :
    let written := Streaming.enter effectWorld restoreAfterWrite
    let quiet := Streaming.enter effectWorld (.symbol "done")
    let left := Streaming.advance emptyRegistry 80 written
    let right := Streaming.advance emptyRegistry 80 quiet
    ∃ (start₁ end₁ start₂ end₂ : Fired (machine emptyRegistry))
        (run₁ : Quiver.Path start₁ end₁) (run₂ : Quiver.Path start₂ end₂),
      Represents start₁ (configOf written) ∧ Represents start₂ (configOf quiet) ∧
      Represents end₁ (configOf left) ∧ Represents end₂ (configOf right) ∧
      left.agenda = [] ∧ right.agenda = [] ∧
      Streaming.values left = [.symbol "done"] ∧ Streaming.values right = [.symbol "done"] ∧
      coreView left.world = coreView right.world ∧
      (observePath (streamedWorld emptyRegistry coreView) run₁).map eraseCut ≠
        (observePath (streamedWorld emptyRegistry coreView) run₂).map eraseCut := by
  intro written quiet left right
  obtain ⟨start₁, rep₁⟩ := exists_represents (configOf written)
  obtain ⟨start₂, rep₂⟩ := exists_represents (configOf quiet)
  obtain ⟨end₁, run₁, _, reached₁, word₁⟩ := advance_world_stream_lifts emptyRegistry coreView 80 rep₁
  obtain ⟨end₂, run₂, _, reached₂, word₂⟩ := advance_world_stream_lifts emptyRegistry coreView 80 rep₂
  refine ⟨start₁, end₁, start₂, end₂, run₁, run₂, rep₁, rep₂, reached₁, reached₂,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [word₁, word₂]
    decide +kernel

/-- Zero fuel retains unfinished work even though a real firing is available. -/
theorem zero_budget_is_not_completion {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (Streaming.enter emptyWorld quotedComputation))) :
    Streaming.run emptyRegistry 0 (Streaming.enter emptyWorld quotedComputation) =
        .suspended (Streaming.enter emptyWorld quotedComputation) ∧
      ∃ final, (stepSystem emptyRegistry).Step store final := by
  refine ⟨rfl, ?_⟩
  have computed : ∃ after, Streaming.step emptyRegistry
      (Streaming.enter emptyWorld quotedComputation) = some after := ⟨_, rfl⟩
  obtain ⟨after, taken⟩ := computed
  obtain ⟨final, fired, _⟩ := (source_bisimulation emptyRegistry).2 represented taken
  exact ⟨final, fired⟩

def zeroDivisorCall : Atom :=
  .expression [.symbol "%", .grounded (.int 1), .grounded (.int 0)]

theorem source_fault_is_not_empty_completion :
    let reached := Streaming.advance emptyRegistry 30 (Streaming.enter emptyWorld zeroDivisorCall)
    Streaming.observe reached = .fault .zeroDivisor reached := by
  rfl

theorem actual_fault_has_target_execution {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (Streaming.enter emptyWorld zeroDivisorCall))) :
    ∃ final, Nonempty (ExecutionPath (stepSystem emptyRegistry) store final) ∧
      ∀ after : State, Represents final (configOf after) →
        Streaming.observe after = .fault .zeroDivisor after := by
  obtain ⟨final, path, _, finalRelated⟩ := advance_lifts emptyRegistry 30 represented
  refine ⟨final, ⟨path⟩, ?_⟩
  intro after related
  rw [representation_unique related finalRelated]
  exact source_fault_is_not_empty_completion

def namedLocation : Atom := .symbol "named-proof"

def namedScalarProgram : Atom := .expression [.symbol "let", .var "before",
  .expression [.symbol "collapse", .expression [.symbol "get-atoms", namedLocation]],
  .expression [.symbol "let", .var "added",
    .expression [.symbol "add-atom", namedLocation, .symbol "scalar"],
    .expression [.symbol "let", .var "present",
      .expression [.symbol "remove-atom", namedLocation, .symbol "scalar"],
      .expression [.symbol "let", .var "absent",
        .expression [.symbol "remove-atom", namedLocation, .symbol "scalar"],
        .expression [.symbol "report", .var "before", .var "added", .var "present", .var "absent"]]]]]

/-- An ordinary atom name starts empty, stores a scalar, and reports actual
removal separately from a later missing-row result. No allocation is needed. -/
theorem named_scalar_lifecycle :
    let reached := Streaming.advance emptyRegistry 100 (Streaming.enter emptyWorld namedScalarProgram)
    reached.agenda = [] ∧
      Streaming.values reached = [.expression [.symbol "report", .expression [],
        Effects.boolean true, Effects.boolean true, Effects.boolean false]] ∧
      reached.world.state.core = [] ∧ reached.world.state.next = 0 := by
  decide +kernel

theorem named_lifecycle_has_target_execution {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (Streaming.enter emptyWorld namedScalarProgram))) :
    ∃ final, Nonempty (ExecutionPath (stepSystem emptyRegistry) store final) ∧
      ∀ after : State, Represents final (configOf after) →
        after.agenda = [] ∧ Streaming.values after = [.expression [.symbol "report", .expression [],
          Effects.boolean true, Effects.boolean true, Effects.boolean false]] ∧
        after.world.state.core = [] ∧ after.world.state.next = 0 := by
  obtain ⟨final, path, _, finalRelated⟩ := advance_lifts emptyRegistry 100 represented
  refine ⟨final, ⟨path⟩, ?_⟩
  intro after related
  rw [representation_unique related finalRelated]
  exact named_scalar_lifecycle

def namedUnboundRemoval : Atom := .expression [.symbol "remove-atom", namedLocation, .var "missing"]

theorem named_unbound_removal_is_a_fault :
    let reached := Streaming.advance emptyRegistry 30 (Streaming.enter emptyWorld namedUnboundRemoval)
    Streaming.observe reached = .fault .instantiation reached ∧
      reached.world.state.namedSpaces = [] := by
  constructor <;> rfl

def namedIsolation : Atom := .expression [.symbol "let", .var "left-made",
  .expression [.symbol "add-atom", .symbol "named-left", seed a],
  .expression [.symbol "let", .var "right-made",
    .expression [.symbol "add-atom", .symbol "named-right", seed b],
    .expression [.symbol "collapse", .expression [.symbol "match", .symbol "named-left",
      seed (.var "found"), .var "found"]]]]

theorem separate_named_spaces_do_not_alias :
    let reached := Streaming.advance emptyRegistry 100 (Streaming.enter emptyWorld namedIsolation)
    reached.agenda = [] ∧ Streaming.values reached = [.expression [a]] ∧
      reached.world.state.namedSpaces.lookup "named-right" = some [seed b] ∧
      reached.world.state.core = [] := by
  decide +kernel


private def arithmeticPayload : Atom :=
  .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]

private def readBody (body : Atom) : Atom :=
  .expression [.symbol "match", .symbol "&self", seed (.var "x"), body]

private def codeWorld : World := { state := NamedSpaces.Store.new [seed arithmeticPayload] [] }

/-- Returning a captured call-shaped value is not the same as splicing that
value into the template as executable syntax; explicit eval still runs it. -/
theorem capture_retains_demand :
    Streaming.values (Streaming.advance emptyRegistry 36 (Streaming.enter codeWorld (readBody (.var "x")))) =
        [arithmeticPayload] ∧
      Streaming.values (Streaming.advance emptyRegistry 36
        (Streaming.enter codeWorld (readBody (.expression [.symbol "eval", .var "x"])))) =
        [.grounded (.int 3)] ∧
      Streaming.values (Streaming.advance emptyRegistry 36 (Streaming.enter codeWorld arithmeticPayload)) =
        [.grounded (.int 3)] := by decide +kernel

private def bothSeeds : Atom := .expression [.symbol ",", seed (.var "x"), seed (.var "x")]

private def removeMatched : Atom := .expression [.symbol "match", .symbol "&self", bothSeeds,
  .expression [.symbol "let", .var "removed",
    .expression [.symbol "remove-atom", .symbol "&self", seed (.var "x")], .var "x"]]

private def onceThenOutside : Atom := .expression [.symbol "superpose",
  .expression [.expression [.symbol "once", removeMatched], .symbol "outside"]]

/-- The second selected body would make a different write. The first
answer cuts that body, not the older alternative outside the delimiter. -/
theorem compound_once_keeps_other_row :
    let all := Streaming.advance emptyRegistry 96 (Streaming.enter effectWorld removeMatched)
    let once := Streaming.advance emptyRegistry 96 (Streaming.enter effectWorld onceThenOutside)
    all.agenda = [] ∧ Streaming.values all = [a,b] ∧ all.world.state.core = [] ∧
      once.agenda = [] ∧ Streaming.values once = [a,.symbol "outside"] ∧
      once.world.state.core = [seed b] := by decide +kernel

theorem compound_once_reaches_the_step {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (Streaming.enter effectWorld onceThenOutside))) :
    ∃ final, ∃ path : ExecutionPath (stepSystem emptyRegistry) store final,
      path.length ≤ 96 ∧ ∀ after : State, Represents final (configOf after) →
        after.agenda = [] ∧ Streaming.values after = [a,.symbol "outside"] ∧
        after.world.state.core = [seed b] := by
  obtain ⟨final,path,steps,there⟩ := advance_lifts emptyRegistry 96 represented
  refine ⟨final,path,steps,fun after readback => ?_⟩
  rw [representation_unique readback there]
  exact compound_once_keeps_other_row.2.2.2

private def onceAfterSilentDeletion : Atom := .expression [.symbol "once",
  .expression [.symbol "match",.symbol "&self",bothSeeds,
    .expression [.symbol "if",.expression [.symbol "==",.var "x",a],
      .expression [.symbol "let",.var "removed",
        .expression [.symbol "remove-atom",.symbol "&self",seed b],.expression [.symbol "empty"]],
      .var "x"]]]

/-- No public answer does not imply no effects. An earlier answerless
body deletes the later witness, but `once` still gets that witness's
retained answer. Reopening its query would find nothing. -/
theorem once_needs_entry_view_after_silent_effect :
    let reached := Streaming.advance emptyRegistry 128 (Streaming.enter effectWorld onceAfterSilentDeletion)
    let reopened := Streaming.advance emptyRegistry 48 (Streaming.enter reached.world
      (.expression [.symbol "match",.symbol "&self",.expression [.symbol ",",seed b,seed b],b]))
    reached.agenda = [] ∧ Streaming.values reached = [b] ∧ reached.world.state.core = [seed a] ∧
      reopened.agenda = [] ∧ Streaming.values reopened = [] := by decide +kernel

private def onceFaultAfterWrite : Atom := .expression [.symbol "once",
  .expression [.symbol "let", .var "removed",
    .expression [.symbol "remove-atom", .symbol "&self", seed a],
    .expression [.symbol "match",.grounded (.int 0),bothSeeds,.var "x"]]]

private def paidFaultObservation : Streaming.Outcome → Option (Bool × List Atom × List Atom)
  | .suspended retained => some (false, Streaming.values retained, retained.world.state.core)
  | .fault .invalidSpace stopped => some (true, Streaming.values stopped, stopped.world.state.core)
  | _ => none

/-- An uncaught fault after a real write is not normal empty completion
and does not roll back the write. Resume the paid cut rather than
re-entering the expression. -/
theorem once_fault_after_write_is_not_exhaustion :
    let start := Streaming.enter effectWorld onceFaultAfterWrite
    let paid := Streaming.advance emptyRegistry 11 start
    let reached := Streaming.advance emptyRegistry 17 start
    paidFaultObservation (Streaming.observe paid) = some (false,[],[seed b]) ∧
      paidFaultObservation (Streaming.observe reached) = some (true,[],[seed b]) ∧
      Streaming.advance emptyRegistry 6 paid = reached := by
  dsimp only
  exact ⟨by decide +kernel,by decide +kernel,
    (Streaming.advance_add emptyRegistry 11 6 _).symm⟩

/-- The retained prefix has already paid for the removal. Resuming
reaches a fault with no new visible event, so the joint word alone
cannot replace the source completion classifier. -/
theorem once_fault_after_write_has_same_word_at_the_cut
    {store : Fired (machine emptyRegistry)}
    (represented : Represents store (configOf (Streaming.enter effectWorld onceFaultAfterWrite))) :
    let start := Streaming.enter effectWorld onceFaultAfterWrite
    let retained := Streaming.advance emptyRegistry 11 start
    let stopped := Streaming.advance emptyRegistry 17 start
    ∃ (cut last : Fired (machine emptyRegistry))
        (first : Quiver.Path store cut) (suffix : Quiver.Path cut last),
      Represents cut (configOf retained) ∧ Represents last (configOf stopped) ∧
      paidFaultObservation (Streaming.observe retained) = some (false,[],[seed b]) ∧
      paidFaultObservation (Streaming.observe stopped) = some (true,[],[seed b]) ∧
      (observePath (streamedWorld emptyRegistry coreView) first).map eraseCut = [([seed b], none)] ∧
      observePath (streamedWorld emptyRegistry coreView) (first.comp suffix) =
        observePath (streamedWorld emptyRegistry coreView) first := by
  intro start retained stopped
  obtain ⟨cut, first, _, waiting, earlier⟩ := advance_world_stream_lifts emptyRegistry coreView 11 represented
  obtain ⟨last, suffix, _, reached, later⟩ := advance_world_stream_lifts emptyRegistry coreView 6 waiting
  have checked := once_fault_after_write_is_not_exhaustion
  have ends : Streaming.advance emptyRegistry 6 retained = stopped := checked.2.2
  have quiet : cutWord emptyRegistry coreView 6 retained = [] :=
    List.eq_nil_of_length_eq_zero (by decide +kernel)
  have completion : Represents last (configOf stopped) :=
    (congrArg (fun state => Represents last (configOf state)) ends).mp reached
  refine ⟨cut, last, first, suffix, waiting, completion, checked.1, checked.2.1, ?_, ?_⟩
  · rw [earlier]
    decide +kernel
  · rw [Mettapedia.Machines.ProgressObservation.observePath_comp, later, quiet, List.append_nil]

private def deletingTemplate : Atom :=
  .expression [.symbol "let", .var "removed",
    .expression [.symbol "remove-atom", .symbol "&self", seed b], .var "x"]

private def removeWhileReading : Atom :=
  .expression [.symbol "match", .symbol "&self", bothSeeds, deletingTemplate]

/-- Even a real take by the first body cannot retroactively retract the
later body selected by the snapshot; the deletion remains in the world. -/
theorem deleted_row_still_runs_captured_body :
    let after := Streaming.advance emptyRegistry 96 (Streaming.enter effectWorld removeWhileReading)
    after.agenda = [] ∧ Streaming.values after = [a, b] ∧
      after.world.state.core = [seed a] := by decide +kernel

/-- Replacing a retained branch with a newly opened join is observable. -/
theorem fresh_join_after_deletion_is_different :
    let after := Streaming.advance emptyRegistry 96 (Streaming.enter effectWorld removeWhileReading)
    let reopened := Streaming.advance emptyRegistry 48
      (Streaming.enter after.world
        (.expression [.symbol "match",.symbol "&self",bothSeeds,.var "x"]))
    reopened.agenda = [] ∧ Streaming.values reopened = [a] := by decide +kernel

theorem deleting_template_after_compound_capture_on_the_step {store : Store Shared PUnit Job Empty}
    (represented : Represents store (configOf (Streaming.enter effectWorld removeWhileReading))) :
    ∃ final, ∃ path : ExecutionPath (stepSystem emptyRegistry) store final,
      path.length ≤ 96 ∧ ∀ after : State, Represents final (configOf after) →
        after.agenda = [] ∧ Streaming.values after = [a,b] ∧ after.world.state.core = [seed a] := by
  obtain ⟨final,path,bound,reached⟩ := advance_lifts emptyRegistry 96 represented
  refine ⟨final,path,bound,fun after readback => ?_⟩
  rw [representation_unique readback reached]
  exact deleted_row_still_runs_captured_body

/-- Repeating a leg preserves the four choices of two physical copies.
The empty conjunction installs one body before touching any rows. -/
theorem compound_capture_duplicates_and_unit :
    let world : World := { state := NamedSpaces.Store.new [seed a,seed a] [] }
    let exec (pattern : Atom) :=
      Streaming.advance emptyRegistry 96
        (Streaming.enter world (.expression [.symbol "match",.symbol "&self",pattern,.symbol "ok"]))
    (exec bothSeeds).agenda = [] ∧
      Streaming.values (exec bothSeeds) = List.replicate 4 (.symbol "ok") ∧
      Streaming.values (exec (.expression [.symbol ","])) = [.symbol "ok"] := by decide +kernel

/-- The same schematic occurrence can be read in two legs with incompatible
ground arguments because its private variables are opened twice. -/
theorem compound_capture_freshens_each_read :
    let world : World := { state := NamedSpaces.Store.new [seed (.var "private")] [] }
    let pattern := .expression [.symbol ",", seed a, seed b]
    let after := Streaming.advance emptyRegistry 48
      (Streaming.enter world (.expression [.symbol "match",.symbol "&self",pattern,.symbol "ok"]))
    after.agenda = [] ∧ Streaming.values after = [.symbol "ok"] := by decide +kernel

section RetainedPull

open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation
open RunsAsFirings (Row rowSupply tracks_load)
open Unifying (queryLegs queryJoin)

/-- Equal-width edits to nonmatching ground rows can reuse the actual
prepared join across different caller supplies. -/
theorem unrelated_replacement_reuses_join :
    queryJoin id [seed a, seed b, .symbol "old-noise"] (queryLegs bothSeeds) [] 0 =
      queryJoin id [seed a, seed b, .symbol "new-noise"] (queryLegs bothSeeds) [] 7 := by
  apply Unifying.queryJoin_ground_reuse id _ _ rfl
    (List.all_eq_true.mp (by decide +kernel)) (List.all_eq_true.mp (by decide +kernel)) _
    _ [] (fun _ impossible => False.elim (List.not_mem_nil impossible))
  intro leg member bindings _
  have shape : leg = seed (.var "x") := by simpa [queryLegs, bothSeeds] using member
  subst leg
  have miss (noise : String) : ∀ row ∈ [Atom.symbol noise],
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (seed (.var "x")) (id row) = none := by
    intro row present
    obtain rfl := List.mem_singleton.mp present
    rfl
  exact
    (Unifying.groundHits_append_unmatched id [seed a, seed b] [.symbol "old-noise"]
      bindings (seed (.var "x")) (miss _)).trans
      (Unifying.groundHits_append_unmatched id [seed a, seed b] [.symbol "new-noise"]
        bindings (seed (.var "x")) (miss _)).symm

/-- The same packets do not license silently reusing the old charge if
an unrelated append enlarged the view. -/
theorem unrelated_append_keeps_packets_but_changes_charge :
    let left := queryJoin id [seed a, seed b] (queryLegs bothSeeds) [] 0
    let right := queryJoin id [seed a, seed b, .symbol "extra"] (queryLegs bothSeeds) [] 7
    left.map Prod.fst = right.map Prod.fst ∧ left.map Prod.snd = some 6 ∧ right.map Prod.snd = some 9 := by
  decide +kernel

private def queryProbe {O : Type} (state : JoinCursor.State O) : Nat :=
  match state.work with
  | .scan _ _ _ _ _ (_ :: _) :: _ => 1
  | _ => 0

/-- Preparing the first path probes only its two chosen rows. The suspended
cursor retains the other physical choices, including duplicate labels. -/
theorem lazy_join_retains_duplicate_paths :
    let worker := JoinCursor.machine (fun _ : Nat => seed a)
    let entrance := JoinCursor.start [0, 1] (queryLegs bothSeeds) [] 0
    let first := worker.run 5 entrance
    first.1.map Prod.fst = [[0, 0]] ∧ worker.spent queryProbe 5 entrance = 2 ∧
      (match first.2 with
      | .exhausted saved =>
          let rest := worker.run 12 saved
          match rest.2 with
          | .finished last => some (saved.view, rest.1.map Prod.fst, last)
          | _ => none
      | _ => none) = some ([0, 1], [[0, 1], [1, 0], [1, 1]], 6) := by
  decide +kernel

/-- The fully executed deletion leaves a live domain that would deny the
saved suffix. Pulling the old view still returns the old second path. -/
theorem lazy_join_does_not_reopen_after_a_write :
    let worker := JoinCursor.machine (id : Atom → Atom)
    let first := worker.run 5 (JoinCursor.start effectWorld.state.core (queryLegs bothSeeds) [] 0)
    let reached := Streaming.advance emptyRegistry 96 (Streaming.enter effectWorld removeWhileReading)
    reached.world.state.core = [seed a] ∧
      (match first.2 with
      | .exhausted saved => some ((worker.run 20 saved).1.map Prod.fst)
      | _ => none) = some [[seed b, seed b]] ∧
      (worker.run 20
        (JoinCursor.start reached.world.state.core (queryLegs bothSeeds) [] reached.world.uses)).1.map
          Prod.fst = [[seed a, seed a]] := by
  decide +kernel

private def capturedOperand : State :=
  at_ effectWorld [.execute ⟨.returned [⟨.symbol "&self", []⟩],
    [.source (.query bothSeeds deletingTemplate)]⟩] []

private def capturedOccurrences := Row.load 0 [seed a, seed b]

private def drainedReadout :=
  (JoinCursor.machine rowSupply.label).run 17
    (JoinCursor.start (rowSupply.rowsAt .self capturedOccurrences) (queryLegs bothSeeds) [] 0)

private theorem closure_of_readout : drainedReadout = (drainedReadout.1, .finished 6) := by
  have status : (match drainedReadout.2 with | .finished value => some value | _ => none) = some 6 := by
    decide +kernel
  apply Prod.ext rfl
  cases observed : drainedReadout.2 <;> simp_all only [Option.some.injEq, reduceCtorEq]

private theorem cursorBatch :
    queryJoin rowSupply.label (rowSupply.rowsAt .self capturedOccurrences)
      (queryLegs bothSeeds) [] 0 = some (drainedReadout.1, 6) :=
  JoinCursor.finished_exact rowSupply.label _ _ _ _ _ closure_of_readout

/-- The real source handoff uses the completed cursor's packets as both
the read receipt and the agenda of the effectful source template. -/
theorem pulled_match_handoff :
    Streaming.Transition emptyRegistry capturedOperand
      (resumeMatch capturedOperand 6 deletingTemplate drainedReadout.1 [] []) ∧
      RunsAsFirings.askStream rowSupply emptyRegistry capturedOccurrences capturedOperand =
        some (joinedRequest drainedReadout.1) := by
  exact written_match_handoff (supply := rowSupply) (registry := emptyRegistry)
    (before := capturedOperand) (ids := capturedOccurrences) (handle := .self)
    (answer := ⟨.symbol "&self", []⟩) (more := []) (packets := drainedReadout.1)
    (pattern := bothSeeds) (body := deletingTemplate) (caller := []) (pending := [])
    (rows := [seed a, seed b]) (used := 6)
    (tracks_load [seed a, seed b]) rfl rfl rfl cursorBatch

/-- Open later legs in the world reached by the earlier template and
the missing witness is observable, even though the outer read retained
its choice of that row. The computation is in the same source evaluator. -/
theorem nested_reads_lose_the_later_witness :
    let authored := nestedAt .self (queryLegs bothSeeds) deletingTemplate
    let reached := Streaming.advance emptyRegistry 96 (Streaming.enter effectWorld authored)
    reached.agenda = [] ∧ Streaming.values reached = [a] ∧ reached.world.state.core = [seed a] := by
  decide +kernel

/-- The other direction of the separation: an effect can supply a
witness to a later per-leg read. The whole-query view excludes it. -/
theorem nested_reads_can_find_a_new_witness :
    let world : World := {state := NamedSpaces.Store.new [seed a, seed b, seen a] []}
    let legs := [seed (.var "x"), seen (.var "x")]
    let body := .expression [.symbol "let", .var "added",
      .expression [.symbol "add-atom", .symbol "&self", seen b], .var "x"]
    let nested := Streaming.advance emptyRegistry 128 (Streaming.enter world (nestedAt .self legs body))
    let captured := Streaming.advance emptyRegistry 128 (Streaming.enter world
      (.expression [.symbol "match", .symbol "&self", .expression (.symbol "," :: legs), body]))
    nested.agenda = [] ∧ captured.agenda = [] ∧
      Streaming.values nested = [a, b] ∧ Streaming.values captured = [a] := by
  decide +kernel

end RetainedPull

section EarlyBodyDemand

open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation
open Mettapedia.Machines.StoreAndDemand
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open RunsAsFirings (Row rowSupply tracks_load)
open Unifying (queryLegs queryJoin groundQueryCharge resolve)

private def lastSeed : Atom := .symbol "c"
private def demandRows : List Atom := [seed a, seed b, seed lastSeed]
private def demandWorld : World := {state := NamedSpaces.Store.new demandRows []}
private def demandIds := Row.load 0 demandRows

private def eraseThen (value result : Atom) : Atom :=
  .expression [.symbol "let", .var "discard",
    .expression [.symbol "remove-atom", .symbol "&self", seed value], result]

private def demandedBody : Atom :=
  .expression [.symbol "if", .expression [.symbol "==", .var "x", a],
    eraseThen a (.expression [.symbol "empty"]), eraseThen (.var "x") (.var "x")]

private def outside : Job := .execute ⟨.evaluate [] (.symbol "outside"), []⟩

private def demandEntry : State :=
  at_ demandWorld [.execute ⟨.evaluate [] (.expression [.symbol "once",
    .expression [.symbol "match", .symbol "&self", bothSeeds, demandedBody]]), []⟩, outside] []

private def demandFront : State := Streaming.advance emptyRegistry 3 demandEntry

private theorem placed_demand : demandFront.agenda =
    [.execute ⟨.returned [⟨.symbol "&self", []⟩], [.source (.query bothSeeds demandedBody), .first 0]⟩,
      .first 0, outside] := rfl

private theorem placed_demand_valid : Streaming.Regions.WellFormed demandFront := by
  apply Streaming.Regions.advance_wellFormed
  simp [demandEntry, outside, Streaming.Regions.WellFormed, Streaming.Regions.valid,
    Streaming.Regions.ordered, Streaming.Regions.markers, List.filterMap, Streaming.Regions.boundary,
    Streaming.Regions.linked, Streaming.Regions.jobFits, Streaming.Regions.framesFit]

private def demandCharge :=
  groundQueryCharge rowSupply.label (rowSupply.rowsAt .self demandIds) (queryLegs bothSeeds) []

private theorem demand_completes :
    ∃ all, queryJoin rowSupply.label (rowSupply.rowsAt .self demandIds) (queryLegs bothSeeds)
      [] demandFront.world.uses = some (all, demandCharge) :=
  Unifying.queryJoin_ground_charge rowSupply.label (rowSupply.rowsAt .self demandIds)
    (List.all_eq_true.mp (by decide +kernel)) (queryLegs bothSeeds) []
    (fun _ impossible => False.elim (List.not_mem_nil impossible)) demandFront.world.uses

private def demandRead :=
  (JoinCursor.machine rowSupply.label).run 13
    (JoinCursor.start (rowSupply.rowsAt .self demandIds) (queryLegs bothSeeds) [] demandFront.world.uses)

private theorem demand_read_paused : ∃ saved, demandRead = (demandRead.1, .exhausted saved) := by
  have pending : (match demandRead.2 with | .exhausted _ => true | _ => false) = true := by decide +kernel
  cases wait : demandRead.2
  case exhausted saved => exact ⟨saved, Prod.ext rfl wait⟩
  all_goals simp [wait] at pending

private def demandWorker := matchBodyPrefix demandFront demandCharge demandedBody demandRead.1

private def paidDemand :=
  Mettapedia.Machines.Cursor.advance
    (FirstAnswer.provider (Streaming.pull emptyRegistry)) (FirstAnswer.client Answer Effects.Fault)
    (fun _ _ => 1) 64 (FirstAnswer.start (Streaming.pull emptyRegistry) demandWorker)

private theorem paid_demand_answer : ∃ (spent : Nat) (answer : Answer) (after : State),
    paidDemand = (spent, .done ⟨(), .answer answer, after⟩) ∧
      resolve answer.bindings answer.value = b ∧ after.world.state.core = [seed lastSeed] := by
  have observed : (match paidDemand.2 with
    | .done result => match result.2.1 with
      | .answer value => some (resolve value.bindings value.value, result.2.2.world.state.core)
      | _ => none
    | .paused _ => none) = some (b, [seed lastSeed]) := by decide +kernel
  cases outcome : paidDemand.2 with
  | paused saved => simp [outcome] at observed
  | done result =>
      rcases result with ⟨index, reply, reached⟩
      cases index
      cases reply
      case answer value =>
        exact ⟨paidDemand.1, value, reached, Prod.ext rfl outcome,
          Prod.mk.inj (Option.some.inj (by simpa only [outcome] using observed))⟩
      all_goals simp [outcome] at observed

/-- The first selected path writes but returns nothing. The second writes
and supplies the first answer. The third path is not prepared by the
cursor and never runs. A job beyond the delimiter remains pending. -/
theorem early_join_cut_preserves_silent_effects_and_older_job :
    demandCharge = 12 ∧ demandRead.1.length = 2 ∧
      ∃ (count : Nat) (answer : Answer) (after : State),
        Streaming.advance emptyRegistry (count + 3) demandFront =
          {after with agenda := [.execute ⟨.returned [answer], []⟩, outside], answers := []} ∧
        resolve answer.bindings answer.value = b ∧ after.world.state.core = [seed lastSeed] := by
  obtain ⟨all, complete⟩ := demand_completes
  obtain ⟨saved, paused⟩ := demand_read_paused
  obtain ⟨spent, answer, after, observed, value, survivors⟩ := paid_demand_answer
  obtain ⟨ready, count, progressed, answered, _⟩ :=
    FirstAnswer.progress_of_answer (Streaming.pull emptyRegistry) 64 observed
  have actual := written_match_cursor_prefix_cut (registry := emptyRegistry)
    (supply := rowSupply) (before := demandFront) (ids := demandIds)
    (location := ⟨.symbol "&self", []⟩) (more := []) (pattern := bothSeeds) (body := demandedBody)
    (handle := .self) (caller := []) (pending := []) (older := [outside])
    (rows := demandRows) (key := 0) (cursorFuel := 13) (earlier := demandRead.1)
    (tracks_load demandRows) placed_demand placed_demand_valid rfl rfl complete paused progressed answered
  exact ⟨by decide +kernel, by decide +kernel, count, answer, after, actual.1, value, survivors⟩

end EarlyBodyDemand

/-- Body multiplicity is not row multiplicity: each matched row may yield
more than one answer, in its own branch and in execution order. -/
theorem each_body_may_yield_several_answers :
    let body := .expression [.symbol "superpose", .expression [.var "x", .var "x"]]
    let after := Streaming.advance emptyRegistry 64 (Streaming.enter effectWorld (readBody body))
    after.agenda = [] ∧ Streaming.values after = [a, a, b, b] := by decide +kernel

private def noExtension : LibTransform.Sources :=
  { kernel := [.pat .take (.var "x")], every := some [.pat .read (.symbol "absent-value")] }

/-- A selected take commits even when there are no continuation packets.
Searching for a first user answer instead would allow another kernel take. -/
theorem answerless_first_commit_keeps_the_later_token :
    match afterFirstCommit (at_ { state := NamedSpaces.Store.new [a, b] [] } [] []) .self
        noExtension (.var "x") [] [] with
    | .ok (some committed) =>
        let after := Streaming.advance emptyRegistry 8 committed
        after.agenda = [] ∧ Streaming.values after = [] ∧ after.world.state.core = [b]
    | _ => False := by
  have fired : LibTransform.fireFirst [a, b] noExtension (templateControls (.var "x")) =
      some ([b], []) := rfl
  have consumed : ([b] : List Atom) ≠ [a, b] := by decide
  simp only [afterFirstCommit, NamedSpaces.Store.read_self, NamedSpaces.Store.new, fired,
    if_neg consumed, NamedSpaces.Store.write]
  decide +kernel

/-- This is a real limit of the library's one-sided matching profile, not a
reason to put the actual written-match handoff behind a groundness guard. -/
theorem open_row_needs_two_sided_selection :
    let rows : List Atom := [.expression [.symbol "same", .var "y", .var "y"]]
    let pattern : Atom := .expression [.symbol "same", a, .var "x"]
    (LibTransform.fireFirst rows (LibTransformStep.allRead pattern)
        (templateControls (.var "x"))).map (fun result => result.2.length) = some 0 ∧
      (Unifying.queryBodies [] pattern (.var "x") 1 rows).map List.length = some 1 := by
  decide +kernel

end Controls

#print axioms onTheStep
#print axioms hosted
#print axioms reachable_world_iff
#print axioms Controls.published_answer
#print axioms Controls.empty_agenda_no_step

end Mettapedia.Languages.MeTTa.PeTTa.StreamingCorrespondence
