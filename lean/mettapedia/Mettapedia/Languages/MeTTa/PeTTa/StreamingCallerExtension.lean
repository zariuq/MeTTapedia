import Mettapedia.Languages.MeTTa.PeTTa.StreamingDemand
import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionPreservation
import Mettapedia.Data.List.FirstSelectionTransport

/-!
# Extending actual streaming work by a caller and older alternatives

The extension preserves the source world's state, I/O, allocations and private
code. Saved collection callers receive the same outer continuation as tasks.
The outer answer history is retained independently of a producer's history.
This is a map on the existing machine state, not another evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.CallerExtension

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def task (caller : List Frame) (source : Task) : Task :=
  ⟨source.control,source.frames ++ caller⟩

def job (caller : List Frame) : Job → Job
  | .execute source => .execute (task caller source)
  | .collect key bindings frames bank => .collect key bindings (frames ++ caller) bank
  | .handler key => .handler key
  | .first key => .first key

def plug (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) (source : State) : State :=
  {source with agenda := source.agenda.map (job caller) ++ older,answers := earned}

theorem first_marker (caller : List Frame) (key : Nat) (source : Job) :
    firstMarker key (job caller source) = firstMarker key source := by cases source <;> rfl

theorem handler_marker (caller : List Frame) (key : Nat) (source : Job) :
    handlerMarker key (job caller source) = handlerMarker key source := by cases source <;> rfl

theorem collection_change (caller : List Frame) (key : Nat) (answer : Unifying.Answer) (source : Job) :
    collectionChange key answer (job caller source) = (collectionChange key answer source).map (job caller) := by
  cases source with
  | execute | handler | first => rfl
  | collect found bindings frames bank =>
      simp only [job,collectionChange]
      split <;> rfl

theorem later_answers (caller : List Frame) (older source : List Job) (answers : List Unifying.Answer)
    (frames : List Frame) :
    (laterAnswers answers frames source).map (job caller) ++ older =
      laterAnswers answers (frames ++ caller) (source.map (job caller) ++ older) := by
  cases answers <;> rfl

theorem handles_append {frames : List Frame} {key : Nat} (found : Handles frames key) (caller : List Frame) :
    Handles (frames ++ caller) key := by
  induction found with
  | here key rest => exact .here key (rest ++ caller)
  | source found ih => exact .source ih
  | collection found ih => exact .collection ih
  | first found ih => exact .first ih

theorem placement_plug {state target : State} {after : Unifying.Configuration}
    {frames : List Frame} {source : List Job}
    (placed : Placement state after frames source target)
    (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) :
    Placement (plug caller older earned state) after (frames ++ caller)
      (source.map (job caller) ++ older) (plug caller older earned target) := by
  cases placed with
  | plain shape => exact .plain shape
  | collection shape => exact .collection shape
  | handler shape => exact .handler shape
  | waiting shape ordinary =>
      simpa only [plug,job,task,List.map_cons,List.cons_append,List.append_assoc] using
        Placement.waiting (state := plug caller older earned state) shape ordinary

theorem delivery_plug {registry : SpaceSemantics.Program} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {source : List Job}
    (delivered : Delivery registry state answer frames source target) (nonempty : frames ≠ [])
    (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) :
    Delivery registry (plug caller older earned state) answer (frames ++ caller)
      (source.map (job caller) ++ older) (plug caller older earned target) := by
  cases delivered with
  | root => exact False.elim (nonempty rfl)
  | source source placement =>
      exact .source source (placement_plug placement caller older earned)
  | collection recorded =>
      exact .collection (recorded.map_append (job caller) (collection_change caller _ _) older)
  | handler key rest source => exact .handler key (rest ++ caller) (source.map (job caller) ++ older)
  | first found => exact .first (found.map_append (job caller) (first_marker caller _) older)

/-- Before the body returns to its root, a real source transition commutes
with adding an outer caller and older alternatives. A root answer is the
one boundary that must instead be delivered to the installed caller. -/
theorem transition_plug {registry : SpaceSemantics.Program} {state target : State}
    (taken : Transition registry state target) (quiet : rootPacket state = none)
    (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) :
    Transition registry (plug caller older earned state) (plug caller older earned target) := by
  cases taken with
  | @collection_done key bindings saved bank pending head =>
    have shape : (plug caller older earned state).agenda =
        .collect key bindings (saved ++ caller) bank :: (pending.map (job caller) ++ older) := by
      simp [plug, head, job]
    simpa only [plug, List.map_cons, List.cons_append, job, task, List.nil_append] using
      Transition.collection_done (registry := registry) shape
  | @handler_done key pending head =>
    have shape : (plug caller older earned state).agenda =
        .handler key :: (pending.map (job caller) ++ older) := by simp [plug, head, job]
    exact Transition.handler_done shape
  | @first_done key pending head =>
    have shape : (plug caller older earned state).agenda =
        .first key :: (pending.map (job caller) ++ older) := by simp [plug, head, job]
    exact Transition.first_done shape
  | @empty frames pending head =>
    have shape : (plug caller older earned state).agenda =
        .execute ⟨.returned [], frames ++ caller⟩ :: (pending.map (job caller) ++ older) := by
      simp [plug, head, job, task]
    exact Transition.empty shape
  | @answer target answer answers frames pending head delivered =>
    have present : frames ≠ [] := by
      rintro rfl
      simp [rootPacket, head] at quiet
    have moved := delivery_plug delivered present caller older earned
    rw [later_answers] at moved
    exact .answer (by simp [plug, head, job, task]) moved
  | @alternatives controls answers frames pending head =>
    have shape : (plug caller older earned state).agenda =
        .execute ⟨.sequence controls answers,frames ++ caller⟩ :: (pending.map (job caller) ++ older) := by
      simp [plug, head, job, task]
    simpa only [plug, later_answers, List.map_append, List.map_map, Function.comp_def, job, task,
      List.append_assoc] using Transition.alternatives (registry := registry) shape
  | @collection_enter bindings expression frames pending head =>
    have shape : (plug caller older earned state).agenda =
        .execute ⟨.evaluate bindings (.expression [.symbol "collapse",expression]),frames ++ caller⟩ ::
          (pending.map (job caller) ++ older) := by simp [plug, head, job, task]
    simpa only [openCollection, plug, List.map_cons, List.cons_append, job, task] using
      Transition.collection_enter (registry := registry) shape
  | @first_enter bindings expression frames pending head =>
    have shape : (plug caller older earned state).agenda =
        .execute ⟨.evaluate bindings (.expression [.symbol "once",expression]),frames ++ caller⟩ ::
          (pending.map (job caller) ++ older) := by simp [plug, head, job, task]
    simpa only [openFirst, plug, List.map_cons, List.cons_append, job, task] using
      Transition.first_enter (registry := registry) shape
  | @caught reason frames pending key remaining head handled closed =>
    have opened : (plug caller older earned state).agenda =
        .execute ⟨.fault reason,frames ++ caller⟩ :: (pending.map (job caller) ++ older) := by
      simp [plug, head, job, task]
    exact .caught opened (handles_append handled caller)
      (closed.map_append (job caller) (handler_marker caller _) older)
  | @phase target current pending reached head ordinary source placed =>
    exact Transition.phase (task := task caller current) (by simp [plug, head, job])
      ordinary source (placement_plug placed caller older earned)

open Mettapedia.Machines.StoreAndDemand

/-- Transport precisely the paid progress, including all effects, without
polling the first packet or replaying any of the completed work. -/
theorem advance_plug_progress {registry : SpaceSemantics.Program} {state target : State} {count : Nat}
    (progress : FirstAnswer.Progress (pull registry) state count target)
    (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) :
    advance registry count (plug caller older earned state) = plug caller older earned target := by
  induction progress with
  | nil => rfl
  | @step before middle after count reply _ ih =>
    obtain ⟨taken,quiet⟩ := progress_exact reply
    have computed := (transition_plug taken quiet caller older earned).computed
    simpa only [advance, Mettapedia.Machines.BoundedDeterministicRun.run.eq_2, computed] using ih

/-! ## First-answer delimitation -/

/-- The producer behind an opened `once`, read without its outer caller.
Reserve the real delimiter's key before running its body, so that further
source allocations agree on both sides of the attachment. -/
def firstBody (before : State) (control : Unifying.Control) : State :=
  {before with
    agenda := [.execute ⟨control,[]⟩]
    answers := []
    nextBoundary := before.nextBoundary + 1}

theorem once_progress_exact {registry : SpaceSemantics.Program} {before ready : State}
    {bindings : Subst} {expression : Atom}
    {caller : List Frame} {older : List Job} {count : Nat}
    (entry : before.agenda = .execute
      ⟨.evaluate bindings (.expression [.symbol "once",expression]),caller⟩ :: older)
    (progress : FirstAnswer.Progress (pull registry) (firstBody before (.evaluate bindings expression)) count ready) :
    advance registry (count + 1) before =
      plug (.first before.nextBoundary :: caller) (.first before.nextBoundary :: older) before.answers ready := by
  have taken := (Transition.first_enter (registry := registry) entry).computed
  have attached : openFirst before (.evaluate bindings expression) caller older =
      plug (.first before.nextBoundary :: caller) (.first before.nextBoundary :: older) before.answers
        (firstBody before (.evaluate bindings expression)) := by
    simp [openFirst,firstBody,plug,job,task]
  rw [attached] at taken
  have lifted := advance_plug_progress progress (.first before.nextBoundary :: caller)
    (.first before.nextBoundary :: older) before.answers
  simpa only [advance, Mettapedia.Machines.BoundedDeterministicRun.run.eq_2, taken] using lifted

private theorem first_suffix (limit key : Nat) (before older : List Job)
    (wellOrdered : Regions.ordered limit (Regions.markers (before ++ .first key :: older))) :
    List.FirstSelection.After (firstMarker key) (before ++ .first key :: older) older := by
  have markers : Regions.ordered limit
      (Regions.markers before ++ .first key :: Regions.markers older) := by
    simpa only [Regions.markers, List.filterMap_append, List.filterMap_cons, Regions.boundary] using wellOrdered
  have noAlias : ∀ job ∈ before, firstMarker key job = false := by
    intro item member
    cases item with
    | execute | collect | handler => rfl
    | first found =>
      have inPrefix : (.first found : Regions.Boundary) ∈ Regions.markers before :=
        Regions.marker_mem_of_job member rfl
      have different : found ≠ key := Regions.ordered_before_key_ne limit (Regions.markers before)
        (.first key) (Regions.markers older) markers _ inPrefix
      simp [firstMarker, different]
  clear markers wellOrdered
  induction before with
  | nil => exact .here (by simp [firstMarker])
  | cons first rest ih =>
    exact .skip (noAlias first (by simp)) (ih (fun item member => noAlias item (by simp [member])))

/-- The first returned packet cuts precisely its own scope and keeps the
producer's reached world. Pending jobs before the marker are also cut;
older jobs after the marker are not. -/
theorem answer_cuts_own_once {registry : SpaceSemantics.Program} {ready after : State}
    {answer : Unifying.Answer} (delivered : pull registry ready = (.answer answer,after))
    (key : Nat) (caller : List Frame) (uninspected older : List Job) (earned : List Unifying.Answer)
    (valid : Regions.WellFormed (plug (.first key :: caller) (uninspected ++ .first key :: older) earned ready)) :
    Transition registry (plug (.first key :: caller) (uninspected ++ .first key :: older) earned ready)
      {after with agenda := .execute ⟨.returned [answer],caller⟩ :: older, answers := earned} := by
  obtain ⟨rest,pending,agenda,rfl⟩ := answer_exact delivered
  let attached := plug (.first key :: caller) (uninspected ++ .first key :: older) earned ready
  let remaining := pending.map (job (.first key :: caller))
  have opening : attached.agenda =
      .execute ⟨.returned (answer :: rest),.first key :: caller⟩ ::
        (remaining ++ (uninspected ++ .first key :: older)) := by
    simp [attached,remaining,plug,agenda,job,task]
  have good := (Regions.head_and_tail valid opening).2
  let tail := (laterAnswers rest [] pending).map (job (.first key :: caller))
  have ordered : Regions.ordered attached.nextBoundary
      (Regions.markers ((tail ++ uninspected) ++ .first key :: older)) := by
    rw [List.append_assoc]
    unfold tail
    rw [later_answers, Regions.markers_later_answers]
    exact good.1
  have cut := first_suffix attached.nextBoundary key (tail ++ uninspected) older ordered
  rw [List.append_assoc] at cut
  unfold tail at cut
  rw [later_answers] at cut
  exact Transition.answer opening (.first cut)

/-- Start just the already supplied controls from the world of an
opened sequence, with no outer caller or answer history attached. -/
def sequencePrefix (before : State) (controls : List Unifying.Control) : State :=
  {before with agenda := controls.map (fun control => .execute ⟨control, []⟩), answers := []}

/-- A witness in the supplied prefix licenses the actual first-answer
boundary of a longer sequence. The skipped controls and pending jobs are
inside this delimiter; no part of them is inspected or run. The source
world at the cut is the one reached by the prefix, including silent
effects, and not a copy of the original world. -/
theorem sequence_prefix_cut_exact {registry : SpaceSemantics.Program} {before ready after : State}
    {earlier later : List Unifying.Control} {count key : Nat} {answer : Unifying.Answer}
    {caller : List Frame} {inside older : List Job}
    (entry : before.agenda =
      .execute ⟨.sequence (earlier ++ later) [], .first key :: caller⟩ ::
        (inside ++ .first key :: older))
    (good : Regions.WellFormed before)
    (progress : FirstAnswer.Progress (pull registry) (sequencePrefix before earlier) count ready)
    (answered : pull registry ready = (.answer answer,after)) :
    advance registry (count + 2) before =
      {after with agenda := .execute ⟨.returned [answer],caller⟩ :: older, answers := before.answers} := by
  let caller' := .first key :: caller
  let uninspected := (later.map fun control => Job.execute ⟨control, caller'⟩) ++ inside
  let opened := plug caller' (uninspected ++ .first key :: older) before.answers (sequencePrefix before earlier)
  have placed : Transition registry before opened := by
    simpa only [opened, uninspected, caller', plug, sequencePrefix, List.map_append, List.map_map,
      Function.comp_def, job, task, List.nil_append, List.append_assoc, laterAnswers] using
      Transition.alternatives (registry := registry) entry
  have taken := placed.computed
  have runPrefix := advance_plug_progress progress caller' (uninspected ++ .first key :: older) before.answers
  have reached : advance registry (count + 1) before =
      plug caller' (uninspected ++ .first key :: older) before.answers ready := by
    simpa only [advance, Mettapedia.Machines.BoundedDeterministicRun.run.eq_2, taken] using runPrefix
  have valid := Regions.advance_wellFormed registry (count + 1) before good
  rw [reached] at valid
  have cut := (answer_cuts_own_once answered key caller uninspected older before.answers valid).computed
  rw [show count + 2 = (count + 1) + 1 from rfl, advance_add, reached]
  simp only [caller', advance, Mettapedia.Machines.BoundedDeterministicRun.run.eq_2, cut,
    Mettapedia.Machines.BoundedDeterministicRun.run.eq_1]

/-- Actual `once` consists of one opening, the paid producer prefix and
one cut. The surviving job returns the original packet to the caller;
neither the world's effects nor the packet's bindings are copied back
from the initial state. -/
theorem once_answer_exact {registry : SpaceSemantics.Program} {before ready after : State}
    {bindings : Subst} {expression : Atom}
    {caller : List Frame} {older : List Job} {count : Nat} {answer : Unifying.Answer}
    (entry : before.agenda = .execute
      ⟨.evaluate bindings (.expression [.symbol "once",expression]),caller⟩ :: older)
    (good : Regions.WellFormed before)
    (progress : FirstAnswer.Progress (pull registry) (firstBody before (.evaluate bindings expression)) count ready)
    (delivered : pull registry ready = (.answer answer,after)) :
    advance registry (count + 2) before =
      {after with agenda := .execute ⟨.returned [answer],caller⟩ :: older, answers := before.answers} := by
  have openedPrefix := once_progress_exact entry progress
  have well := Regions.advance_wellFormed registry (count + 1) before good
  rw [openedPrefix] at well
  have cut := (answer_cuts_own_once delivered before.nextBoundary caller [] older before.answers well).computed
  simp only [List.nil_append] at cut
  rw [show count + 2 = (count + 1) + 1 from rfl, advance_add, openedPrefix]
  simp only [advance, Mettapedia.Machines.BoundedDeterministicRun.run.eq_2, cut,
    Mettapedia.Machines.BoundedDeterministicRun.run.eq_1]

/-- No answer is produced if the paid body really finishes without a
root reply. It releases the delimiter and keeps its effects. A mere
paused body does not satisfy the empty-agenda premise. -/
theorem once_empty_exact {registry : SpaceSemantics.Program} {before ready : State}
    {bindings : Subst} {expression : Atom}
    {caller : List Frame} {older : List Job} {count : Nat}
    (entry : before.agenda = .execute
      ⟨.evaluate bindings (.expression [.symbol "once",expression]),caller⟩ :: older)
    (progress : FirstAnswer.Progress (pull registry) (firstBody before (.evaluate bindings expression)) count ready)
    (finished : ready.agenda = []) :
    advance registry (count + 2) before = {ready with agenda := older,answers := before.answers} := by
  rw [show count + 2 = (count + 1) + 1 from rfl, advance_add, once_progress_exact entry progress]
  simp [advance, Mettapedia.Machines.BoundedDeterministicRun.run, step, plug, finished]

private theorem nearest_append_when_none (inner outer : List Frame)
    (notHandled : nearestHandler inner = none) :
    nearestHandler (inner ++ outer) = nearestHandler outer := by
  induction inner with
  | nil => rfl
  | cons frame rest ih => cases frame <;> simp_all [nearestHandler]

/-- First-answer demand is not a fault handler. An uncaught fault remains
visible at the paid cut unless a real enclosing handler accepts it. -/
theorem once_uncaught_exact {registry : SpaceSemantics.Program} {before ready : State}
    {bindings : Subst} {expression : Atom} {caller frames : List Frame}
    {older pending : List Job} {count : Nat} {reason : Effects.Fault}
    (entry : before.agenda = .execute
      ⟨.evaluate bindings (.expression [.symbol "once",expression]),caller⟩ :: older)
    (progress : FirstAnswer.Progress (pull registry) (firstBody before (.evaluate bindings expression)) count ready)
    (fault : ready.agenda = .execute ⟨.fault reason,frames⟩ :: pending)
    (noInner : nearestHandler frames = none) (noOuter : nearestHandler caller = none) :
    let cut := plug (.first before.nextBoundary :: caller) (.first before.nextBoundary :: older) before.answers ready
    observe (advance registry (count + 1) before) = .fault reason cut := by
  have noHandler : nearestHandler (frames ++ .first before.nextBoundary :: caller) = none :=
    (nearest_append_when_none frames _ noInner).trans noOuter
  simp [once_progress_exact entry progress, observe, plug, fault, job, task, noHandler]

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.CallerExtension
