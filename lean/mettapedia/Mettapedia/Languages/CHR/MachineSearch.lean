import Mettapedia.Languages.CHR.MachineMatching

/-! The machine's partner search as an enumeration. `selections` lists the
complete selections a search reaches from one head position, in search order;
`pending` lists those still ahead of a frame stack. Each search tick either
leaves `pending` unchanged while a finite measure decreases, or hands the
first pending selection to `complete`, or finds nothing pending. A resumable
search therefore decides exactly as a single pass over `pending` would. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

section Enumeration

variable (store : Store) (position active : Nat) (values : List Value)

/-- The complete selections reached from the head at `index`, in search order. -/
def selections : Nat → List Head → Environment → List Pick → List Nat → List (Environment × List Pick)
  | _, [], environment, picks, _ => [(environment, picks)]
  | index, head :: later, environment, picks, used =>
    (candidates index position active values head store).flatMap fun candidate =>
      if candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active) then []
      else
        match matchTerms head.arguments candidate.values environment with
        | none => []
        | some bound =>
          selections (index + 1) later bound (picks ++ [⟨Head.key head, candidate.id⟩]) (candidate.id :: used)

/-- What one candidate for the head at `index` contributes. -/
def contribution (index : Nat) (head : Head) (later : List Head) (environment : Environment)
    (picks : List Pick) (used : List Nat) (candidate : Occ) : List (Environment × List Pick) :=
  if candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active) then []
  else
    match matchTerms head.arguments candidate.values environment with
    | none => []
    | some bound =>
      selections store position active values (index + 1) later bound
        (picks ++ [⟨Head.key head, candidate.id⟩]) (candidate.id :: used)

theorem selections_cons (index : Nat) (head : Head) (later : List Head) (environment : Environment)
    (picks : List Pick) (used : List Nat) :
    selections store position active values index (head :: later) environment picks used =
      (candidates index position active values head store).flatMap
        (contribution store position active values index head later environment picks used) := by
  rw [selections]
  rfl

/-- The complete selections still ahead of one frame. -/
def frameSelections (frame : Frame) : List (Environment × List Pick) :=
  match frame.heads with
  | [] => []
  | head :: later =>
    frame.candidates.flatMap
      (contribution store position active values frame.index head later frame.environment frame.picks frame.used)

/-- The complete selections still ahead of a frame stack, in search order. -/
def pending (frames : List Frame) : List (Environment × List Pick) :=
  frames.flatMap (frameSelections store position active values)

/-- The frame a search starts with, as `scan` builds it, has every selection
of the occurrence pending. -/
theorem pending_start (head : Head) (later : List Head) :
    pending store position active values
        [⟨0, head :: later, candidates 0 position active values head store, [], [], []⟩] =
      selections store position active values 0 (head :: later) [] [] [] := by
  simp [pending, frameSelections, selections_cons]

end Enumeration

/-! ## One search tick -/

/-- What one search tick does to a frame stack: continue silently with new
frames, hand a complete selection to `complete` and keep the rest, or find
nothing left. -/
inductive Move where
  | silent (frames : List Frame)
  | produce (environment : Environment) (picks : List Pick) (stay : List Frame)
  | exhausted

def move (store : Store) (position active : Nat) (values : List Value) : List Frame → Move
  | [] => .exhausted
  | frame :: below =>
    match frame.candidates with
    | [] => .silent below
    | candidate :: others =>
      let stay := { frame with candidates := others } :: below
      if candidate.id ∈ frame.used ∨ (frame.index ≠ position ∧ candidate.id = active) then .silent stay
      else
        match frame.heads with
        | [] => .silent stay
        | head :: later =>
          match matchTerms head.arguments candidate.values frame.environment with
          | none => .silent stay
          | some bound =>
            let chosen := frame.picks ++ [⟨Head.key head, candidate.id⟩]
            match later with
            | [] => .produce bound chosen stay
            | nextHead :: _ =>
              .silent (⟨frame.index + 1, later,
                candidates (frame.index + 1) position active values nextHead store,
                bound, chosen, candidate.id :: frame.used⟩ :: stay)

/-- The machine's search step is the move of its frame stack. -/
theorem search_move (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (frames : List Frame) (tail : List Task) (state : State) :
    search active key values occurrence after frames tail state =
      match move state.store occurrence.head active values frames with
      | .silent next => { state with tasks := .search active key values occurrence after next :: tail }
      | .produce environment picks stay => complete active key values occurrence after stay environment picks tail state
      | .exhausted => { state with tasks := .scan active key values after :: tail } := by
  unfold search move
  rcases frames with _ | ⟨frame, below⟩
  · rfl
  · rcases frame with ⟨index, heads, candidates', environment, picks, used⟩
    rcases candidates' with _ | ⟨candidate, others⟩
    · rfl
    · dsimp only
      by_cases rejected : candidate.id ∈ used ∨ (index ≠ occurrence.head ∧ candidate.id = active)
      · simp only [rejected, if_true]
      · simp only [rejected, if_false]
        rcases heads with _ | ⟨head, later⟩
        · rfl
        · dsimp only
          cases matchTerms head.arguments candidate.values environment with
          | none => rfl
          | some bound =>
            rcases later with _ | ⟨nextHead, rest⟩ <;> rfl

/-- A silent move keeps every pending selection; a producing move hands over
the first one and keeps the others; an exhausted stack has none. -/
theorem pending_move (store : Store) (position active : Nat) (values : List Value) (frames : List Frame) :
    match move store position active values frames with
    | .silent next => pending store position active values next = pending store position active values frames
    | .produce environment picks stay =>
        pending store position active values frames =
          (environment, picks) :: pending store position active values stay
    | .exhausted => pending store position active values frames = [] := by
  unfold move
  rcases frames with _ | ⟨frame, below⟩
  · rfl
  · rcases frame with ⟨index, heads, candidates', environment, picks, used⟩
    rcases candidates' with _ | ⟨candidate, others⟩
    · simp [pending, frameSelections]
      cases heads <;> rfl
    · dsimp only
      by_cases rejected : candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active)
      · simp only [rejected, if_true]
        rcases heads with _ | ⟨head, later⟩
        · simp [pending, frameSelections]
        · simp [pending, frameSelections, contribution, rejected]
      · simp only [rejected, if_false]
        rcases heads with _ | ⟨head, later⟩
        · simp [pending, frameSelections]
        · dsimp only
          cases matched : matchTerms head.arguments candidate.values environment with
          | none => simp [pending, frameSelections, contribution, rejected, matched]
          | some bound =>
            rcases later with _ | ⟨nextHead, rest⟩
            · simp [pending, frameSelections, contribution, rejected, matched, selections]
            · simp [pending, frameSelections, contribution, rejected, matched, selections_cons]

#print axioms search_move
#print axioms pending_move

end Mettapedia.Languages.CHR.Machine
