import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes

/-!
# Region links in the actual streaming frontier

Markers are ordered by their actual allocation identities. A task's saved
frames refer to later markers in that order; collection frames retain the
exact caller stored by their marker. Source frames do not introduce markers.
The propositions describe the existing agenda and allocate no runtime table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions

inductive Boundary where
  | collection (key : Nat) (caller : List Frame)
  | handler (key : Nat)
  | first (key : Nat)

def Boundary.key : Boundary → Nat
  | .collection key _ | .handler key | .first key => key

def boundary : Job → Option Boundary
  | .execute _ => none
  | .collect key _ caller _ => some (.collection key caller)
  | .handler key => some (.handler key)
  | .first key => some (.first key)

def markers (agenda : List Job) : List Boundary := agenda.filterMap boundary

/-- Allocation order is strict even across markers of different kinds. -/
def ordered (limit : Nat) : List Boundary → Prop
  | [] => True
  | scope :: rest => scope.key < limit ∧ ordered scope.key rest

/-- Each marker in the frame stack is found after the previous one. An old
callee handler may remain on the agenda after returning to its outer caller. -/
def framesFit : List Boundary → List Frame → Prop
  | _,[] => True
  | scopes,.source _ :: caller => framesFit scopes caller
  | scopes,.collection key :: caller =>
      ∃ before after, scopes = before ++ .collection key caller :: after ∧ framesFit after caller
  | scopes,.handler key :: caller =>
      ∃ before after, scopes = before ++ .handler key :: after ∧ framesFit after caller
  | scopes,.first key :: caller =>
      ∃ before after, scopes = before ++ .first key :: after ∧ framesFit after caller

def jobFits (scopes : List Boundary) : Job → Prop
  | .execute task => framesFit scopes task.frames
  | .collect _ _ caller _ => framesFit scopes caller
  | .handler _ | .first _ => True

def linked : List Job → Prop
  | [] => True
  | job :: older => jobFits (markers older) job ∧ linked older

def valid (limit : Nat) (agenda : List Job) : Prop := ordered limit (markers agenda) ∧ linked agenda

def WellFormed (state : State) : Prop := valid state.nextBoundary state.agenda

theorem ordered_mono {first second : Nat} {scopes : List Boundary}
    (increase : first ≤ second) (good : ordered first scopes) : ordered second scopes := by
  cases scopes with
  | nil => trivial
  | cons scope rest => exact ⟨good.1.trans_le increase,good.2⟩

theorem ordered_key_lt {limit : Nat} {scopes : List Boundary} (good : ordered limit scopes) :
    ∀ scope ∈ scopes, scope.key < limit := by
  induction scopes generalizing limit with
  | nil => simp
  | cons first rest ih =>
      intro scope present
      rcases List.mem_cons.mp present with rfl | later
      · exact good.1
      · exact (ih good.2 scope later).trans good.1

theorem ordered_key_unique {limit : Nat} {scopes : List Boundary} (good : ordered limit scopes)
    {left right : Boundary} (leftPresent : left ∈ scopes) (rightPresent : right ∈ scopes)
    (same : left.key = right.key) : left = right := by
  induction scopes generalizing limit with
  | nil => cases leftPresent
  | cons first rest ih =>
      rcases List.mem_cons.mp leftPresent with rfl | laterLeft
      · rcases List.mem_cons.mp rightPresent with rfl | laterRight
        · rfl
        · have smaller := ordered_key_lt good.2 right laterRight
          exact False.elim ((Nat.ne_of_lt smaller) same.symm)
      · rcases List.mem_cons.mp rightPresent with rfl | laterRight
        · have smaller := ordered_key_lt good.2 left laterLeft
          exact False.elim ((Nat.ne_of_lt smaller) same)
        · exact ih good.2 laterLeft laterRight

theorem ordered_keys_nodup {limit : Nat} {scopes : List Boundary} (good : ordered limit scopes) :
    (scopes.map Boundary.key).Nodup := by
  induction scopes generalizing limit with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih good.2⟩
      intro present
      obtain ⟨scope,inRest,same⟩ := List.mem_map.mp present
      exact (Nat.ne_of_lt (ordered_key_lt good.2 scope inRest)) same

theorem ordered_suffix (limit : Nat) (before after : List Boundary)
    (good : ordered limit (before ++ after)) : ordered limit after := by
  induction before generalizing limit with
  | nil => exact good
  | cons first rest ih => exact ordered_mono (Nat.le_of_lt good.1) (ih first.key good.2)

theorem ordered_before_key_ne (limit : Nat) (before : List Boundary) (chosen : Boundary)
    (after : List Boundary) (good : ordered limit (before ++ chosen :: after)) :
    ∀ scope ∈ before, scope.key ≠ chosen.key := by
  induction before generalizing limit with
  | nil => simp
  | cons first rest ih =>
      intro scope present
      rcases List.mem_cons.mp present with rfl | later
      · have smaller := ordered_key_lt good.2 chosen (List.mem_append_right _ List.mem_cons_self)
        exact (Nat.ne_of_lt smaller).symm
      · exact ih first.key good.2 scope later

theorem frames_prefix (before : List Boundary) {scopes : List Boundary} {frames : List Frame}
    (good : framesFit scopes frames) : framesFit (before ++ scopes) frames := by
  induction frames generalizing scopes with
  | nil => trivial
  | cons frame caller ih =>
      cases frame with
      | source frame => exact ih good
      | collection key | handler key | first key =>
          obtain ⟨left,right,shape,tailFit⟩ := good
          exact ⟨before ++ left,right,by rw [shape,List.append_assoc],tailFit⟩

theorem frames_tail {scopes : List Boundary} {frame : Frame} {caller : List Frame}
    (good : framesFit scopes (frame :: caller)) : framesFit scopes caller := by
  cases frame with
  | source frame => exact good
  | collection key =>
      obtain ⟨before,after,rfl,tailFit⟩ := good
      have extended := frames_prefix (before ++ [.collection key caller]) tailFit
      rw [List.append_assoc,List.singleton_append] at extended
      exact extended
  | handler key =>
      obtain ⟨before,after,rfl,tailFit⟩ := good
      have extended := frames_prefix (before ++ [.handler key]) tailFit
      rw [List.append_assoc,List.singleton_append] at extended
      exact extended
  | first key =>
      obtain ⟨before,after,rfl,tailFit⟩ := good
      have extended := frames_prefix (before ++ [.first key]) tailFit
      rw [List.append_assoc,List.singleton_append] at extended
      exact extended

theorem linked_suffix (before after : List Job) (good : linked (before ++ after)) : linked after := by
  induction before with
  | nil => exact good
  | cons first rest ih => exact ih good.2

theorem valid_suffix (limit : Nat) (before after : List Job)
    (good : valid limit (before ++ after)) : valid limit after := by
  exact ⟨ordered_suffix limit (markers before) (markers after)
    (by simpa only [markers,List.filterMap_append] using good.1),linked_suffix before after good.2⟩

theorem valid_tail {limit : Nat} {job : Job} {older : List Job}
    (good : valid limit (job :: older)) : valid limit older :=
  valid_suffix limit [job] older good

theorem valid_execute {limit : Nat} {older : List Job} {control : Unifying.Control}
    {frames : List Frame} (pending : valid limit older) (caller : framesFit (markers older) frames) :
    valid limit (.execute ⟨control,frames⟩ :: older) := ⟨pending.1,caller,pending.2⟩

theorem markers_later_answers (answers : List Unifying.Answer) (frames : List Frame) (older : List Job) :
    markers (laterAnswers answers frames older) = markers older := by cases answers <;> rfl

theorem valid_later_answers (answers : List Unifying.Answer) {limit : Nat} {frames : List Frame}
    {older : List Job} (pending : valid limit older) (caller : framesFit (markers older) frames) :
    valid limit (laterAnswers answers frames older) := by
  cases answers with
  | nil => exact pending
  | cons first rest => exact valid_execute pending caller

theorem markers_alternatives (controls : List Unifying.Control) (frames : List Frame) (older : List Job) :
    markers ((controls.map fun control => .execute ⟨control,frames⟩) ++ older) = markers older := by
  induction controls with
  | nil => rfl
  | cons first rest ih => exact ih

theorem valid_alternatives (controls : List Unifying.Control) {limit : Nat} {frames : List Frame}
    {older : List Job} (pending : valid limit older) (caller : framesFit (markers older) frames) :
    valid limit ((controls.map fun control => .execute ⟨control,frames⟩) ++ older) := by
  induction controls with
  | nil => exact pending
  | cons first rest ih =>
      apply valid_execute ih
      simpa only [markers_alternatives] using caller

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions
