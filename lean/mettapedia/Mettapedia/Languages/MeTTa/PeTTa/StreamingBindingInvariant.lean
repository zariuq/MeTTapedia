import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement
import Mettapedia.Data.List.FirstSelectionInvariant

/-!
# Binding invariants across the complete streaming frontier

Each pending control, saved source frame, collection accumulator and completed
answer retains idempotent bindings refining the original record. Marker-only
frames contain no substitution. The predicates describe construction laws;
they introduce no runtime validation pass.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.BindingInvariant

open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def frameRefines (initial : Subst) : Frame → Prop
  | .source frame => Unifying.FrameRefines initial frame
  | .collection _ | .handler _ | .first _ => True

def framesRefine (initial : Subst) (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, frameRefines initial frame

def taskRefines (initial : Subst) (task : Task) : Prop :=
  Unifying.ControlRefines initial task.control ∧ framesRefine initial task.frames

def jobRefines (initial : Subst) : Job → Prop
  | .execute task => taskRefines initial task
  | .collect _ bindings caller answers =>
      Unifying.BindingRefines initial bindings ∧ framesRefine initial caller ∧
        ∀ answer ∈ answers, Unifying.BindingRefines initial answer.bindings
  | .handler _ | .first _ => True

def agendaRefines (initial : Subst) (agenda : List Job) : Prop :=
  ∀ job ∈ agenda, jobRefines initial job

def stateRefines (initial : Subst) (state : State) : Prop :=
  agendaRefines initial state.agenda ∧
    ∀ answer ∈ state.answers, Unifying.BindingRefines initial answer.bindings

theorem frames_cons (initial : Subst) (first : Frame) (rest : List Frame) :
    framesRefine initial (first :: rest) ↔ frameRefines initial first ∧ framesRefine initial rest := by
  simp only [framesRefine,List.mem_cons,forall_eq_or_imp]

theorem agenda_cons (initial : Subst) (first : Job) (rest : List Job) :
    agendaRefines initial (first :: rest) ↔ jobRefines initial first ∧ agendaRefines initial rest := by
  simp only [agendaRefines,List.mem_cons,forall_eq_or_imp]

theorem later_answers (initial : Subst) (answers : List Unifying.Answer) (frames : List Frame) (older : List Job)
    (packets : ∀ answer ∈ answers, Unifying.BindingRefines initial answer.bindings)
    (caller : framesRefine initial frames) (pending : agendaRefines initial older) :
    agendaRefines initial (laterAnswers answers frames older) := by
  cases answers with
  | nil => exact pending
  | cons first rest =>
      apply (agenda_cons _ _ _).mpr
      refine ⟨⟨?_,caller⟩,pending⟩
      simpa only [Unifying.ControlRefines] using packets

theorem collection_change (initial : Subst) (key : Nat) (answer : Unifying.Answer)
    (validAnswer : Unifying.BindingRefines initial answer.bindings)
    (first next : Job) (valid : jobRefines initial first)
    (changed : collectionChange key answer first = some next) : jobRefines initial next := by
  cases first with
  | execute | handler | first => cases changed
  | collect found bindings caller answers =>
      simp only [collectionChange] at changed
      split at changed
      · cases changed
        obtain ⟨saved,frames,packets⟩ := valid
        refine ⟨saved,frames,?_⟩
        intro packet present
        rcases List.mem_append.mp present with previous | added
        · exact packets packet previous
        · have same := List.mem_singleton.mp added
          subst packet
          exact validAnswer
      · cases changed

theorem collection_record (initial : Subst) (key : Nat) (answer : Unifying.Answer)
    (validAnswer : Unifying.BindingRefines initial answer.bindings) (older changed : List Job)
    (pending : agendaRefines initial older)
    (recorded : List.FirstSelection.Change (collectionChange key answer) older changed) :
    agendaRefines initial changed :=
  recorded.preserves_all (jobRefines initial) pending (collection_change initial key answer validAnswer)

theorem selected_suffix (initial : Subst) (selected : Job → Bool) (older remaining : List Job)
    (pending : agendaRefines initial older) (found : List.FirstSelection.After selected older remaining) :
    agendaRefines initial remaining := found.preserves_all (jobRefines initial) pending

theorem open_collection (initial : Subst) (state : State) (bindings : Subst)
    (control : Unifying.Control) (caller : List Frame) (older : List Job)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.BindingRefines initial answer.bindings)
    (saved : Unifying.BindingRefines initial bindings) (active : Unifying.ControlRefines initial control)
    (frames : framesRefine initial caller) (pending : agendaRefines initial older) :
    stateRefines initial (openCollection state bindings control caller older) := by
  refine ⟨(agenda_cons _ _ _).mpr ⟨?_,(agenda_cons _ _ _).mpr ⟨?_,pending⟩⟩,rootAnswers⟩
  · exact ⟨active,(frames_cons _ _ _).mpr ⟨trivial,frames⟩⟩
  · exact ⟨saved,frames,by simp⟩

theorem open_handler (initial : Subst) (state : State) (control : Unifying.Control)
    (caller : List Frame) (older : List Job)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.BindingRefines initial answer.bindings)
    (active : Unifying.ControlRefines initial control)
    (frames : framesRefine initial caller) (pending : agendaRefines initial older) :
    stateRefines initial (openHandler state control caller older) := by
  refine ⟨(agenda_cons _ _ _).mpr ⟨?_,(agenda_cons _ _ _).mpr ⟨trivial,pending⟩⟩,rootAnswers⟩
  exact ⟨active,(frames_cons _ _ _).mpr ⟨trivial,frames⟩⟩

theorem open_first (initial : Subst) (state : State) (control : Unifying.Control)
    (caller : List Frame) (older : List Job)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.BindingRefines initial answer.bindings)
    (active : Unifying.ControlRefines initial control)
    (frames : framesRefine initial caller) (pending : agendaRefines initial older) :
    stateRefines initial (openFirst state control caller older) := by
  refine ⟨(agenda_cons _ _ _).mpr ⟨?_,(agenda_cons _ _ _).mpr ⟨trivial,pending⟩⟩,rootAnswers⟩
  exact ⟨active,(frames_cons _ _ _).mpr ⟨trivial,frames⟩⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.BindingInvariant
