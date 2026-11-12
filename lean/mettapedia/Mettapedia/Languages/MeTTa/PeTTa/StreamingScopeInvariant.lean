import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixScopes
import Mettapedia.Data.List.FirstSelectionInvariant

/-!
# Allocated variable support across the streaming world and frontier

The whole agenda, saved source frames, collection banks, output and retained
cells participate. Public rows, private clauses and unread input remain source
templates copied at their existing boundaries. This adds no reserved spelling
or runtime scan. Region-marker association is a separate invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.ScopeInvariant

def frameSupported (allowed : String → Prop) : Frame → Prop
  | .source frame => Unifying.FrameSupported allowed frame
  | .collection _ | .handler _ | .first _ => True

def framesSupported (allowed : String → Prop) (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, frameSupported allowed frame

def taskSupported (allowed : String → Prop) (task : Task) : Prop :=
  Unifying.ControlSupported allowed task.control ∧ framesSupported allowed task.frames

def jobSupported (allowed : String → Prop) : Job → Prop
  | .execute task => taskSupported allowed task
  | .collect _ bindings caller answers =>
      Unifying.SupportedBindings allowed bindings ∧ framesSupported allowed caller ∧
        ∀ answer ∈ answers, Unifying.AnswerSupported allowed answer
  | .handler _ | .first _ => True

def agendaSupported (allowed : String → Prop) (agenda : List Job) : Prop :=
  ∀ job ∈ agenda, jobSupported allowed job

def worldSupported (allowed : String → Prop) (world : World) : Prop :=
  Unifying.CellsSupported allowed world.state ∧ ∀ output ∈ world.output, Unifying.Supported allowed output

def stateSupported (allowed : String → Prop) (state : State) : Prop :=
  worldSupported allowed state.world ∧ agendaSupported allowed state.agenda ∧
    ∀ answer ∈ state.answers, Unifying.AnswerSupported allowed answer

def WellScoped (state : State) : Prop := stateSupported (Mettapedia.ScopedString.Before state.world.uses) state

theorem frames_cons (allowed : String → Prop) (first : Frame) (rest : List Frame) :
    framesSupported allowed (first :: rest) ↔ frameSupported allowed first ∧ framesSupported allowed rest := by
  simp only [framesSupported,List.mem_cons,forall_eq_or_imp]

theorem agenda_cons (allowed : String → Prop) (first : Job) (rest : List Job) :
    agendaSupported allowed (first :: rest) ↔ jobSupported allowed first ∧ agendaSupported allowed rest := by
  simp only [agendaSupported,List.mem_cons,forall_eq_or_imp]

theorem frame_mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {frame : Frame} (good : frameSupported first frame) : frameSupported later frame := by
  cases frame with
  | source => exact good.mono included
  | _ => trivial

theorem frames_mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {frames : List Frame} (good : framesSupported first frames) : framesSupported later frames :=
  fun frame present => frame_mono included (good frame present)

theorem job_mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {job : Job} (good : jobSupported first job) : jobSupported later job := by
  cases job with
  | execute task => exact ⟨Unifying.ControlSupported.mono included task.control good.1,frames_mono included good.2⟩
  | collect key bindings caller answers =>
      exact ⟨good.1.mono included,frames_mono included good.2.1,fun answer present => (good.2.2 answer present).mono included⟩
  | _ => trivial

theorem agenda_mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {agenda : List Job} (good : agendaSupported first agenda) : agendaSupported later agenda :=
  fun job present => job_mono included (good job present)

theorem world_mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {world : World} (good : worldSupported first world) : worldSupported later world :=
  ⟨fun name value stored => (good.1 name value stored).mono included,
    fun value present => (good.2 value present).mono included⟩

theorem state_mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {state : State} (good : stateSupported first state) : stateSupported later state :=
  ⟨world_mono included good.1,agenda_mono included good.2.1,
    fun answer present => (good.2.2 answer present).mono included⟩

theorem later_answers (allowed : String → Prop) (answers : List Unifying.Answer) (frames : List Frame) (older : List Job)
    (packets : ∀ answer ∈ answers, Unifying.AnswerSupported allowed answer)
    (caller : framesSupported allowed frames) (pending : agendaSupported allowed older) :
    agendaSupported allowed (laterAnswers answers frames older) := by
  cases answers with
  | nil => exact pending
  | cons first rest =>
      refine (agenda_cons _ _ _).mpr ⟨⟨?_,caller⟩,pending⟩
      simpa only [Unifying.ControlSupported] using packets

theorem collection_change (allowed : String → Prop) (key : Nat) (answer : Unifying.Answer)
    (validAnswer : Unifying.AnswerSupported allowed answer) (first next : Job)
    (good : jobSupported allowed first) (changed : collectionChange key answer first = some next) :
    jobSupported allowed next := by
  cases first with
  | execute | handler | first => cases changed
  | collect found bindings caller answers =>
      simp only [collectionChange] at changed
      split at changed
      · cases changed
        refine ⟨good.1,good.2.1,?_⟩
        intro packet present
        rcases List.mem_append.mp present with previous | added
        · exact good.2.2 packet previous
        · have same := List.mem_singleton.mp added
          subst packet
          exact validAnswer
      · cases changed

theorem collection_record (allowed : String → Prop) (key : Nat) (answer : Unifying.Answer)
    (validAnswer : Unifying.AnswerSupported allowed answer) (older changed : List Job)
    (pending : agendaSupported allowed older)
    (recorded : List.FirstSelection.Change (collectionChange key answer) older changed) :
    agendaSupported allowed changed :=
  recorded.preserves_all (jobSupported allowed) pending (collection_change allowed key answer validAnswer)

theorem selected_suffix (allowed : String → Prop) (selected : Job → Bool) (older remaining : List Job)
    (pending : agendaSupported allowed older) (found : List.FirstSelection.After selected older remaining) :
    agendaSupported allowed remaining := found.preserves_all (jobSupported allowed) pending

theorem open_collection (allowed : String → Prop) (state : State)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (control : Unifying.Control)
    (caller : List Frame) (older : List Job) (world : worldSupported allowed state.world)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.AnswerSupported allowed answer)
    (saved : Unifying.SupportedBindings allowed bindings) (active : Unifying.ControlSupported allowed control)
    (frames : framesSupported allowed caller) (pending : agendaSupported allowed older) :
    stateSupported allowed (openCollection state bindings control caller older) := by
  refine ⟨world,(agenda_cons _ _ _).mpr ⟨⟨active,?_⟩,(agenda_cons _ _ _).mpr ⟨?_,pending⟩⟩,rootAnswers⟩
  · exact (frames_cons _ _ _).mpr ⟨trivial,frames⟩
  · exact ⟨saved,frames,by simp⟩

theorem open_handler (allowed : String → Prop) (state : State) (control : Unifying.Control)
    (caller : List Frame) (older : List Job) (world : worldSupported allowed state.world)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.AnswerSupported allowed answer)
    (active : Unifying.ControlSupported allowed control)
    (frames : framesSupported allowed caller) (pending : agendaSupported allowed older) :
    stateSupported allowed (openHandler state control caller older) := by
  exact ⟨world,(agenda_cons _ _ _).mpr ⟨⟨active,(frames_cons _ _ _).mpr ⟨trivial,frames⟩⟩,
    (agenda_cons _ _ _).mpr ⟨trivial,pending⟩⟩,rootAnswers⟩

theorem open_first (allowed : String → Prop) (state : State) (control : Unifying.Control)
    (caller : List Frame) (older : List Job) (world : worldSupported allowed state.world)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.AnswerSupported allowed answer)
    (active : Unifying.ControlSupported allowed control)
    (frames : framesSupported allowed caller) (pending : agendaSupported allowed older) :
    stateSupported allowed (openFirst state control caller older) := by
  exact ⟨world,(agenda_cons _ _ _).mpr ⟨⟨active,(frames_cons _ _ _).mpr ⟨trivial,frames⟩⟩,
    (agenda_cons _ _ _).mpr ⟨trivial,pending⟩⟩,rootAnswers⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.ScopeInvariant
